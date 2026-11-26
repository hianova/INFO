#!/usr/bin/env python3
"""
INFO v1.0.0 — Lossless Hash-Consed Proof-DAG Binary Codec (.infp v1 & Chunked v2)
=================================================================================
Transposes `lean_expr_export.lean export-dag` (`lean-proof-dag-v1`) JSON into:
  - `.infp v1`: sparse topological delta-varint columns + front-coded symbol pools
  - `.infp v2`: Theorem-13 Tiered Hot-Node DAG Macro Hoisting (`local_k=32`,
    `hot_min=3`), specialized single-byte opcodes, tag-stratified sub-columns,
    optional lossless `induct_groups`/`def_meta` kernel metadata, and fixed
    <= 2 MiB chunked framing compatible with arbitrary-size Lean libraries while
    still decompressing exclusively via the unmodified 34,072 B zero-heap
    `./build/info_decomp` binary with 100% SHA-256 bit-exact verification.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_INFO_BIN = ROOT / "build" / "info"
DEFAULT_DECOMP_BIN = ROOT / "build" / "info_decomp"
INFO_MAX_BYTES = 4 * 1024 * 1024
DEFAULT_CHUNK_SIZE = 2 * 1024 * 1024

INFP_MAGIC = b"INFP"
INFP_VERSION_1 = 1
INFP_VERSION_2 = 2
INFP_V1_HEADER = struct.Struct("<4sHHII32s")  # magic, ver=1, flags, raw_col_len, inf1_len, sha256 (48 B)
INFP_V2_HEADER = struct.Struct("<4sHHIQ32s")  # magic, ver=2, flags, num_chunks, raw_col_len, sha256 (52 B)
INFP_CHUNK_HEADER = struct.Struct("<II")      # chunk_raw_len, chunk_inf1_len (8 B)

DECL_KINDS = ("thm", "def", "opaque", "axiom", "induct", "ctor", "rec", "quot")
DECL_KIND_TO_ID = {k: i for i, k in enumerate(DECL_KINDS)}

CHILD_A_TAGS = frozenset((5, 6, 7, 8, 10, 11, 12))
CHILD_B_TAGS = frozenset((5, 6, 7, 8, 12))
HAS_B_TAGS = frozenset((4, 5, 6, 7, 8, 9, 10, 11, 12))
HAS_C_TAGS = frozenset((6, 7, 8, 11))

V2_LOCAL_K = 32
V2_HOT_MIN = 3


def canonical_dag_bytes(dag: Dict[str, Any]) -> bytes:
    """Return canonical deterministic UTF-8 JSON bytes for exact SHA-256 identity checks."""
    return json.dumps(dag, ensure_ascii=False, separators=(",", ":"), sort_keys=True).encode("utf-8")


def canonical_dag_sha256(dag: Dict[str, Any]) -> bytes:
    """Return 32-byte SHA-256 digest of the canonical Proof-DAG JSON."""
    return hashlib.sha256(canonical_dag_bytes(dag)).digest()


def put_uvarint(out: bytearray, value: int) -> None:
    """Append unsigned LEB128 varint."""
    if value < 0:
        raise ValueError(f"Expected non-negative varint, got {value}")
    v = int(value)
    while v >= 0x80:
        out.append((v & 0x7F) | 0x80)
        v >>= 7
    out.append(v)


def get_uvarint(buf: bytes, pos: int) -> Tuple[int, int]:
    """Decode unsigned LEB128 varint starting at `pos`, returning `(value, next_pos)`."""
    val = 0
    shift = 0
    n = len(buf)
    while pos < n:
        b = buf[pos]
        pos += 1
        val |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            return val, pos
        shift += 7
        if shift > 256:
            raise ValueError("Varint overflow in .infp columnar stream")
    raise ValueError("Truncated varint in .infp columnar stream")


def put_front_strings(out: bytearray, strings: Sequence[str]) -> None:
    """Front-code UTF-8 string list relative to the immediately preceding entry."""
    prev = b""
    for s in strings:
        raw = s.encode("utf-8")
        limit = min(len(prev), len(raw))
        lcp = 0
        while lcp < limit and prev[lcp] == raw[lcp]:
            lcp += 1
        suffix = raw[lcp:]
        put_uvarint(out, lcp)
        put_uvarint(out, len(suffix))
        out.extend(suffix)
        prev = raw


def get_front_strings(buf: bytes, pos: int, count: int) -> Tuple[List[str], int]:
    """Decode `count` front-coded UTF-8 strings."""
    out: List[str] = []
    prev = b""
    for _ in range(count):
        lcp, pos = get_uvarint(buf, pos)
        slen, pos = get_uvarint(buf, pos)
        if lcp > len(prev) or pos + slen > len(buf):
            raise ValueError("Corrupt front-coded string entry in .infp stream")
        raw = prev[:lcp] + buf[pos : pos + slen]
        pos += slen
        out.append(raw.decode("utf-8"))
        prev = raw
    return out, pos


def _encode_pools_and_levels(out: bytearray, dag: Dict[str, Any]) -> None:
    put_front_strings(out, [str(dag["format"]), str(dag["module"]), str(dag["prefix"])])

    str_pool: List[str] = dag["str_pool"]
    consts: List[str] = dag["consts"]
    levels: List[List[int]] = dag["levels"]
    level_lists: List[List[int]] = dag["level_lists"]

    put_uvarint(out, len(str_pool))
    put_front_strings(out, str_pool)

    put_uvarint(out, len(consts))
    put_front_strings(out, consts)

    put_uvarint(out, len(levels))
    lvl_tags = bytearray()
    lvl_a = bytearray()
    lvl_b = bytearray()
    for t, a, b in levels:
        if t < 0 or t > 5:
            raise ValueError(f"Invalid level tag {t}")
        lvl_tags.append(t)
        if t == 0:
            if a != 0 or b != 0:
                raise ValueError(f"Non-zero fields on Level.zero: {(t, a, b)}")
        else:
            put_uvarint(lvl_a, a)
            if t in (2, 3):
                put_uvarint(lvl_b, b)
            elif b != 0:
                raise ValueError(f"Unexpected level col_b on tag {t}: {b}")
    out.extend(lvl_tags)
    out.extend(lvl_a)
    out.extend(lvl_b)

    put_uvarint(out, len(level_lists))
    ll_lens = bytearray()
    ll_vals = bytearray()
    for xs in level_lists:
        put_uvarint(ll_lens, len(xs))
        for x in xs:
            put_uvarint(ll_vals, x)
    out.extend(ll_lens)
    out.extend(ll_vals)


def _decode_pools_and_levels(
    raw: bytes,
) -> Tuple[str, str, str, List[str], List[str], List[List[int]], List[List[int]], int]:
    pos = 0
    hdr_strs, pos = get_front_strings(raw, pos, 3)
    fmt, mod_name, prefix = hdr_strs

    n_str, pos = get_uvarint(raw, pos)
    str_pool, pos = get_front_strings(raw, pos, n_str)

    n_const, pos = get_uvarint(raw, pos)
    consts, pos = get_front_strings(raw, pos, n_const)

    n_lvl, pos = get_uvarint(raw, pos)
    if pos + n_lvl > len(raw):
        raise ValueError("Truncated level tags")
    lvl_tags = raw[pos : pos + n_lvl]
    pos += n_lvl

    lvl_a_vals: List[int] = []
    for t in lvl_tags:
        if t == 0:
            lvl_a_vals.append(0)
        else:
            a, pos = get_uvarint(raw, pos)
            lvl_a_vals.append(a)
    levels: List[List[int]] = []
    for i, t in enumerate(lvl_tags):
        b = 0
        if t in (2, 3):
            b, pos = get_uvarint(raw, pos)
        levels.append([t, lvl_a_vals[i], b])

    n_ll, pos = get_uvarint(raw, pos)
    ll_lens: List[int] = []
    for _ in range(n_ll):
        ln, pos = get_uvarint(raw, pos)
        ll_lens.append(ln)
    level_lists: List[List[int]] = []
    for ln in ll_lens:
        xs: List[int] = []
        for _ in range(ln):
            v, pos = get_uvarint(raw, pos)
            xs.append(v)
        level_lists.append(xs)

    return fmt, mod_name, prefix, str_pool, consts, levels, level_lists, pos


def _encode_decls(out: bytearray, decls: List[Dict[str, Any]]) -> None:
    put_uvarint(out, len(decls))
    put_front_strings(out, [str(d["name"]) for d in decls])
    decl_kinds = bytearray()
    decl_lp_lens = bytearray()
    decl_lp_vals = bytearray()
    decl_types = bytearray()
    decl_vals = bytearray()
    for d in decls:
        k = str(d["kind"])
        if k not in DECL_KIND_TO_ID:
            raise ValueError(f"Unknown decl kind {k!r}")
        decl_kinds.append(DECL_KIND_TO_ID[k])
        lps = d["lparams"]
        put_uvarint(decl_lp_lens, len(lps))
        for lp in lps:
            put_uvarint(decl_lp_vals, int(lp))
        put_uvarint(decl_types, int(d["type"]))
        v = d["val"]
        put_uvarint(decl_vals, 0 if v is None else int(v) + 1)

    out.extend(decl_kinds)
    out.extend(decl_lp_lens)
    out.extend(decl_lp_vals)
    out.extend(decl_types)
    out.extend(decl_vals)


def _decode_decls(raw: bytes, pos: int) -> Tuple[List[Dict[str, Any]], int]:
    n_decls, pos = get_uvarint(raw, pos)
    decl_names, pos = get_front_strings(raw, pos, n_decls)
    if pos + n_decls > len(raw):
        raise ValueError("Truncated decl kinds")
    decl_kind_ids = raw[pos : pos + n_decls]
    pos += n_decls

    lp_lens: List[int] = []
    for _ in range(n_decls):
        ln, pos = get_uvarint(raw, pos)
        lp_lens.append(ln)
    decl_lparams: List[List[int]] = []
    for ln in lp_lens:
        xs_lp: List[int] = []
        for _ in range(ln):
            v, pos = get_uvarint(raw, pos)
            xs_lp.append(v)
        decl_lparams.append(xs_lp)

    decl_types: List[int] = []
    for _ in range(n_decls):
        t_id, pos = get_uvarint(raw, pos)
        decl_types.append(t_id)

    decl_vals: List[Optional[int]] = []
    for _ in range(n_decls):
        v_raw, pos = get_uvarint(raw, pos)
        decl_vals.append(None if v_raw == 0 else v_raw - 1)

    decls: List[Dict[str, Any]] = []
    for i in range(n_decls):
        k_id = decl_kind_ids[i]
        if k_id >= len(DECL_KINDS):
            raise ValueError(f"Invalid decl kind id {k_id}")
        decls.append(
            {
                "name": decl_names[i],
                "kind": DECL_KINDS[k_id],
                "lparams": decl_lparams[i],
                "type": decl_types[i],
                "val": decl_vals[i],
            }
        )
    return decls, pos


def _compute_stats(nodes: List[List[int]], decls: List[Dict[str, Any]]) -> Dict[str, int]:
    n_nodes = len(nodes)
    tree_sizes: List[int] = [0] * n_nodes
    for nid, (tag, a, b, _) in enumerate(nodes):
        if tag in (5, 6, 7, 8):
            tree_sizes[nid] = 1 + tree_sizes[a] + tree_sizes[b]
        elif tag == 12:
            tree_sizes[nid] = tree_sizes[a] + tree_sizes[b]
        elif tag in (10, 11):
            tree_sizes[nid] = 1 + tree_sizes[a]
        else:
            tree_sizes[nid] = 1

    total_tree_nodes = 0
    for d in decls:
        total_tree_nodes += tree_sizes[d["type"]]
        if d["val"] is not None:
            total_tree_nodes += tree_sizes[d["val"]]
    return {
        "decl_count": len(decls),
        "global_dag_nodes": len(nodes),
        "total_tree_nodes": total_tree_nodes,
    }


def _encode_kernel_meta(out: bytearray, dag: Dict[str, Any]) -> None:
    has_meta = ("induct_groups" in dag) or ("def_meta" in dag)
    if not has_meta:
        out.append(0)
        return
    out.append(1)
    induct_groups: List[Dict[str, Any]] = dag.get("induct_groups", [])
    def_meta: List[List[Any]] = dag.get("def_meta", [])

    put_uvarint(out, len(induct_groups))
    for g in induct_groups:
        lps = g["lparams"]
        put_uvarint(out, len(lps))
        for lp in lps:
            put_uvarint(out, int(lp))
        put_uvarint(out, int(g["nparams"]))
        out.append(1 if g["is_unsafe"] else 0)
        types = g["types"]
        put_uvarint(out, len(types))
        for tp in types:
            put_front_strings(out, [str(tp["name"])])
            put_uvarint(out, int(tp["type"]))
            ctors = tp["ctors"]
            put_uvarint(out, len(ctors))
            put_front_strings(out, [str(ct[0]) for ct in ctors])
            for ct in ctors:
                put_uvarint(out, int(ct[1]))

    put_uvarint(out, len(def_meta))
    for dm in def_meta:
        put_uvarint(out, int(dm[0]))
        put_uvarint(out, int(dm[1]))
        put_uvarint(out, int(dm[2]))
        put_uvarint(out, int(dm[3]))
        all_names = [str(nm) for nm in dm[4]]
        put_uvarint(out, len(all_names))
        put_front_strings(out, all_names)


def _decode_kernel_meta(raw: bytes, pos: int) -> Tuple[Optional[List[Dict[str, Any]]], Optional[List[List[Any]]], int]:
    if pos >= len(raw):
        return None, None, pos
    flag = raw[pos]
    pos += 1
    if flag == 0:
        return None, None, pos
    if flag != 1:
        raise ValueError(f"Invalid kernel_meta flag byte {flag}")

    n_ig, pos = get_uvarint(raw, pos)
    induct_groups: List[Dict[str, Any]] = []
    for _ in range(n_ig):
        n_lp, pos = get_uvarint(raw, pos)
        lps: List[int] = []
        for _ in range(n_lp):
            v, pos = get_uvarint(raw, pos)
            lps.append(v)
        nparams, pos = get_uvarint(raw, pos)
        is_unsafe = raw[pos] != 0
        pos += 1
        n_types, pos = get_uvarint(raw, pos)
        types: List[Dict[str, Any]] = []
        for _ in range(n_types):
            tnames, pos = get_front_strings(raw, pos, 1)
            t_ty, pos = get_uvarint(raw, pos)
            n_ct, pos = get_uvarint(raw, pos)
            cnames, pos = get_front_strings(raw, pos, n_ct)
            ctors: List[List[Any]] = []
            for cn in cnames:
                ct_ty, pos = get_uvarint(raw, pos)
                ctors.append([cn, ct_ty])
            types.append({"name": tnames[0], "type": t_ty, "ctors": ctors})
        induct_groups.append(
            {"lparams": lps, "nparams": nparams, "is_unsafe": is_unsafe, "types": types}
        )

    n_dm, pos = get_uvarint(raw, pos)
    def_meta: List[List[Any]] = []
    for _ in range(n_dm):
        d_idx, pos = get_uvarint(raw, pos)
        saf, pos = get_uvarint(raw, pos)
        hk, pos = get_uvarint(raw, pos)
        hh, pos = get_uvarint(raw, pos)
        n_an, pos = get_uvarint(raw, pos)
        all_names, pos = get_front_strings(raw, pos, n_an)
        def_meta.append([d_idx, saf, hk, hh, all_names])

    return induct_groups, def_meta, pos


def encode_dag_columnar(dag: Dict[str, Any]) -> bytes:
    """Encode `lean-proof-dag-v1` object into `.infp v1` lossless sparse columnar bytes."""
    if dag.get("format") != "lean-proof-dag-v1":
        raise ValueError(f"Unsupported DAG format: {dag.get('format')!r}")

    out = bytearray()
    _encode_pools_and_levels(out, dag)

    nodes: List[List[int]] = dag["nodes"]
    put_uvarint(out, len(nodes))
    node_tags = bytearray()
    node_a = bytearray()
    node_b = bytearray()
    node_c = bytearray()
    for nid, (tag, a, b, c) in enumerate(nodes):
        if tag < 0 or tag > 12:
            raise ValueError(f"Invalid Expr DAG tag {tag} at nid={nid}")
        node_tags.append(tag)
        if tag in CHILD_A_TAGS:
            if a < 0 or a >= nid:
                raise ValueError(f"Non-topological col_a at nid={nid}, tag={tag}, a={a}")
            put_uvarint(node_a, nid - a)
        else:
            put_uvarint(node_a, a)

        if tag in CHILD_B_TAGS:
            if b < 0 or b >= nid:
                raise ValueError(f"Non-topological col_b at nid={nid}, tag={tag}, b={b}")
            put_uvarint(node_b, nid - b)
        elif tag in HAS_B_TAGS:
            put_uvarint(node_b, b)
        elif b != 0:
            raise ValueError(f"Unexpected col_b on tag {tag}: {b}")

        if tag in HAS_C_TAGS:
            put_uvarint(node_c, c)
        elif c != 0:
            raise ValueError(f"Unexpected col_c on tag {tag}: {c}")

    out.extend(node_tags)
    out.extend(node_a)
    out.extend(node_b)
    out.extend(node_c)
    _encode_decls(out, dag["decls"])
    if ("induct_groups" in dag) or ("def_meta" in dag):
        _encode_kernel_meta(out, dag)
    return bytes(out)


def decode_dag_columnar(raw: bytes) -> Dict[str, Any]:
    """Decode `.infp v1` sparse columnar bytes back into exact `lean-proof-dag-v1` JSON object."""
    fmt, mod_name, prefix, str_pool, consts, levels, level_lists, pos = _decode_pools_and_levels(raw)

    n_nodes, pos = get_uvarint(raw, pos)
    if pos + n_nodes > len(raw):
        raise ValueError("Truncated node tags")
    node_tags = raw[pos : pos + n_nodes]
    pos += n_nodes

    col_a: List[int] = []
    for nid, tag in enumerate(node_tags):
        va, pos = get_uvarint(raw, pos)
        col_a.append(nid - va if tag in CHILD_A_TAGS else va)

    col_b: List[int] = []
    for nid, tag in enumerate(node_tags):
        if tag in CHILD_B_TAGS:
            vb, pos = get_uvarint(raw, pos)
            col_b.append(nid - vb)
        elif tag in HAS_B_TAGS:
            vb, pos = get_uvarint(raw, pos)
            col_b.append(vb)
        else:
            col_b.append(0)

    col_c: List[int] = []
    for tag in node_tags:
        if tag in HAS_C_TAGS:
            vc, pos = get_uvarint(raw, pos)
            col_c.append(vc)
        else:
            col_c.append(0)

    nodes: List[List[int]] = [
        [int(node_tags[i]), col_a[i], col_b[i], col_c[i]] for i in range(n_nodes)
    ]
    decls, pos = _decode_decls(raw, pos)
    ig, dm, pos = _decode_kernel_meta(raw, pos)

    if pos != len(raw):
        raise ValueError(f"Trailing bytes in columnar v1 stream: pos={pos} != len={len(raw)}")

    out: Dict[str, Any] = {
        "format": fmt,
        "module": mod_name,
        "prefix": prefix,
        "stats": _compute_stats(nodes, decls),
        "str_pool": str_pool,
        "consts": consts,
        "levels": levels,
        "level_lists": level_lists,
        "nodes": nodes,
        "decls": decls,
    }
    if ig is not None:
        out["induct_groups"] = ig
    if dm is not None:
        out["def_meta"] = dm
    return out


def encode_dag_v2(
    dag: Dict[str, Any],
    local_k: int = V2_LOCAL_K,
    hot_min: int = V2_HOT_MIN,
) -> Tuple[bytes, int]:
    """Encode `lean-proof-dag-v1` into `.infp v2` columns with Tiered Hot-Node Macros."""
    if dag.get("format") != "lean-proof-dag-v1":
        raise ValueError(f"Unsupported DAG format: {dag.get('format')!r}")

    out = bytearray()
    _encode_pools_and_levels(out, dag)

    nodes: List[List[int]] = dag["nodes"]
    rc: collections.Counter[int] = collections.Counter()
    for nid, (tag, a, b, _) in enumerate(nodes):
        if tag == 5:
            da = nid - a
            db = nid - b
            if (da == 1 and db == 2) or (da == 2 and db == 1):
                continue
            if da == 1:
                if db > local_k:
                    rc[b] += 1
                continue
            if db == 1:
                if da > local_k:
                    rc[a] += 1
                continue
            if da > local_k:
                rc[a] += 1
            if db > local_k:
                rc[b] += 1
        else:
            if tag in CHILD_A_TAGS and (nid - a) > local_k:
                rc[a] += 1
            if tag in CHILD_B_TAGS and (nid - b) > local_k:
                rc[b] += 1

    t1_cap = max(0, 128 - local_k)
    ranked = [nid for nid, cnt in rc.most_common() if cnt >= hot_min]
    t1 = ranked[:t1_cap]
    t2 = sorted(ranked[t1_cap:])
    hot_nodes = t1 + t2
    hot_rank = {nid: idx for idx, nid in enumerate(hot_nodes)}
    hot_count = len(hot_nodes)

    put_uvarint(out, local_k)
    put_uvarint(out, len(t1))
    put_uvarint(out, len(t2))
    for hn in t1:
        put_uvarint(out, hn)
    prev = 0
    for hn in t2:
        put_uvarint(out, hn - prev)
        prev = hn

    def put_ptr(buf: bytearray, nid: int, ch: int) -> None:
        if ch < 0 or ch >= nid:
            raise ValueError(f"Non-topological pointer ch={ch} >= nid={nid}")
        d = nid - ch
        if d <= local_k:
            put_uvarint(buf, d - 1)
        elif ch in hot_rank:
            put_uvarint(buf, local_k + hot_rank[ch])
        else:
            put_uvarint(buf, local_k + hot_count + (d - local_k - 1))

    op_stream = bytearray()
    s_bvar = bytearray()
    s_const_c = bytearray()
    s_const_ll = bytearray()
    s_app_da = bytearray()
    s_app_db = bytearray()
    s_bind_da = bytearray()
    s_bind_db = bytearray()
    s_bind_c = bytearray()
    s_other_a = bytearray()
    s_other_b = bytearray()
    s_other_c = bytearray()

    for nid, (tag, a, b, cc) in enumerate(nodes):
        if tag < 0 or tag > 12:
            raise ValueError(f"Invalid Expr DAG tag {tag} at nid={nid}")
        if tag == 0 and a < 8 and b == 0 and cc == 0:
            op_stream.append(13 + a)
            continue
        if tag == 5 and cc == 0:
            da = nid - a
            db = nid - b
            if da == 1 and db == 2:
                op_stream.append(21)
                continue
            if da == 2 and db == 1:
                op_stream.append(22)
                continue
            if da == 1:
                op_stream.append(23)
                put_ptr(s_app_db, nid, b)
                continue
            if db == 1:
                op_stream.append(24)
                put_ptr(s_app_da, nid, a)
                continue
            op_stream.append(5)
            put_ptr(s_app_da, nid, a)
            put_ptr(s_app_db, nid, b)
            continue
        if tag == 4 and b == 0 and cc == 0:
            op_stream.append(25)
            put_uvarint(s_const_c, a)
            continue

        op_stream.append(tag)
        if tag == 0:
            put_uvarint(s_bvar, a)
        elif tag == 4:
            put_uvarint(s_const_c, a)
            put_uvarint(s_const_ll, b)
        elif tag in (6, 7):
            put_ptr(s_bind_da, nid, a)
            put_ptr(s_bind_db, nid, b)
            put_uvarint(s_bind_c, cc)
        elif tag in (8, 12):
            put_ptr(s_other_a, nid, a)
            put_ptr(s_other_b, nid, b)
            if tag == 8:
                put_uvarint(s_other_c, cc)
        elif tag in (10, 11):
            put_ptr(s_other_a, nid, a)
            put_uvarint(s_other_b, b)
            if tag == 11:
                put_uvarint(s_other_c, cc)
        else:
            put_uvarint(s_other_a, a)
            if tag in HAS_B_TAGS:
                put_uvarint(s_other_b, b)
            if tag in HAS_C_TAGS:
                put_uvarint(s_other_c, cc)

    put_uvarint(out, len(op_stream))
    out.extend(op_stream)

    sub_streams = (
        s_bvar,
        s_const_c,
        s_const_ll,
        s_app_da,
        s_app_db,
        s_bind_da,
        s_bind_db,
        s_bind_c,
        s_other_a,
        s_other_b,
        s_other_c,
    )
    for sub in sub_streams:
        put_uvarint(out, len(sub))
    for sub in sub_streams:
        out.extend(sub)

    _encode_decls(out, dag["decls"])
    _encode_kernel_meta(out, dag)
    return bytes(out), hot_count


def decode_dag_v2(raw: bytes) -> Dict[str, Any]:
    """Decode `.infp v2` sparse tiered-macro bytes back into canonical Proof-DAG dict."""
    fmt, mod_name, prefix, str_pool, consts, levels, level_lists, pos = _decode_pools_and_levels(raw)

    local_k, pos = get_uvarint(raw, pos)
    n_t1, pos = get_uvarint(raw, pos)
    n_t2, pos = get_uvarint(raw, pos)
    hot_nodes: List[int] = []
    for _ in range(n_t1):
        hn, pos = get_uvarint(raw, pos)
        hot_nodes.append(hn)
    prev = 0
    for _ in range(n_t2):
        delta, pos = get_uvarint(raw, pos)
        hn = prev + delta
        hot_nodes.append(hn)
        prev = hn
    hot_count = len(hot_nodes)

    n_nodes, pos = get_uvarint(raw, pos)
    if pos + n_nodes > len(raw):
        raise ValueError("Truncated v2 op_stream")
    op_stream = raw[pos : pos + n_nodes]
    pos += n_nodes

    sub_lens: List[int] = []
    for _ in range(11):
        ln, pos = get_uvarint(raw, pos)
        sub_lens.append(ln)
    sub_slices: List[bytes] = []
    for ln in sub_lens:
        if pos + ln > len(raw):
            raise ValueError("Truncated v2 sub-column")
        sub_slices.append(raw[pos : pos + ln])
        pos += ln
    sub_pos = [0] * 11

    def next_u(idx: int) -> int:
        v, np = get_uvarint(sub_slices[idx], sub_pos[idx])
        sub_pos[idx] = np
        return v

    def next_ptr(idx: int, nid: int) -> int:
        code = next_u(idx)
        if code < local_k:
            return nid - (code + 1)
        if code < local_k + hot_count:
            return hot_nodes[code - local_k]
        d = (code - local_k - hot_count) + local_k + 1
        return nid - d

    nodes: List[List[int]] = []
    for nid, op in enumerate(op_stream):
        if 13 <= op <= 20:
            nodes.append([0, op - 13, 0, 0])
        elif op == 21:
            nodes.append([5, nid - 1, nid - 2, 0])
        elif op == 22:
            nodes.append([5, nid - 2, nid - 1, 0])
        elif op == 23:
            b = next_ptr(4, nid)
            nodes.append([5, nid - 1, b, 0])
        elif op == 24:
            a = next_ptr(3, nid)
            nodes.append([5, a, nid - 1, 0])
        elif op == 25:
            a = next_u(1)
            nodes.append([4, a, 0, 0])
        elif op == 0:
            nodes.append([0, next_u(0), 0, 0])
        elif op == 4:
            nodes.append([4, next_u(1), next_u(2), 0])
        elif op == 5:
            nodes.append([5, next_ptr(3, nid), next_ptr(4, nid), 0])
        elif op in (6, 7):
            nodes.append([op, next_ptr(5, nid), next_ptr(6, nid), next_u(7)])
        elif op == 8:
            nodes.append([8, next_ptr(8, nid), next_ptr(9, nid), next_u(10)])
        elif op == 12:
            nodes.append([12, next_ptr(8, nid), next_ptr(9, nid), 0])
        elif op == 10:
            nodes.append([10, next_ptr(8, nid), next_u(9), 0])
        elif op == 11:
            nodes.append([11, next_ptr(8, nid), next_u(9), next_u(10)])
        else:
            a = next_u(8)
            b = next_u(9) if op in HAS_B_TAGS else 0
            cc = next_u(10) if op in HAS_C_TAGS else 0
            nodes.append([op, a, b, cc])

    for idx in range(11):
        if sub_pos[idx] != len(sub_slices[idx]):
            raise ValueError(f"Unconsumed bytes in v2 sub-column {idx}: {sub_pos[idx]} != {len(sub_slices[idx])}")

    decls, pos = _decode_decls(raw, pos)
    ig, dm, pos = _decode_kernel_meta(raw, pos)
    if pos != len(raw):
        raise ValueError(f"Trailing bytes in columnar v2 stream: pos={pos} != len={len(raw)}")

    out: Dict[str, Any] = {
        "format": fmt,
        "module": mod_name,
        "prefix": prefix,
        "stats": _compute_stats(nodes, decls),
        "str_pool": str_pool,
        "consts": consts,
        "levels": levels,
        "level_lists": level_lists,
        "nodes": nodes,
        "decls": decls,
    }
    if ig is not None:
        out["induct_groups"] = ig
    if dm is not None:
        out["def_meta"] = dm
    return out


def _ring0_compress_chunk(raw_chunk: bytes, info_bin: Path, tmp_dir: Path, idx: int) -> bytes:
    if len(raw_chunk) == 0 or len(raw_chunk) > INFO_MAX_BYTES:
        raise ValueError(f"Chunk {idx} size {len(raw_chunk)} exceeds Ring-0 limit ({INFO_MAX_BYTES} B)")
    p_raw = tmp_dir / f"chunk_{idx}.col"
    p_inf = tmp_dir / f"chunk_{idx}.inf"
    p_raw.write_bytes(raw_chunk)
    res = subprocess.run(
        [str(info_bin), "compress", str(p_raw), str(p_inf)],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        raise RuntimeError(f"info compress failed on chunk {idx} (rc={res.returncode}): {res.stderr.strip()}")
    return p_inf.read_bytes()


def pack_dag_to_infp(
    dag: Dict[str, Any],
    out_infp: Path,
    info_bin: Path = DEFAULT_INFO_BIN,
    raw_json_bytes: Optional[int] = None,
    version: int = INFP_VERSION_2,
    chunk_size: int = DEFAULT_CHUNK_SIZE,
) -> Dict[str, Any]:
    """Encode Proof-DAG into `.infp` v1 or chunked `.infp` v2 via Ring-0 `./build/info`."""
    if not info_bin.is_file():
        raise FileNotFoundError(f"Missing INFO CLI binary: {info_bin}")
    if chunk_size <= 0 or chunk_size > INFO_MAX_BYTES:
        raise ValueError(f"chunk_size {chunk_size} must be in 1..{INFO_MAX_BYTES}")

    sha_digest = canonical_dag_sha256(dag)
    raw_len = raw_json_bytes if raw_json_bytes is not None else len(canonical_dag_bytes(dag))
    out_infp.parent.mkdir(parents=True, exist_ok=True)

    if version == INFP_VERSION_1:
        col_bytes = encode_dag_columnar(dag)
        with tempfile.TemporaryDirectory(prefix="infp_pack1_") as td:
            inf1_bytes = _ring0_compress_chunk(col_bytes, info_bin, Path(td), 0)
        header = INFP_V1_HEADER.pack(
            INFP_MAGIC, INFP_VERSION_1, 0, len(col_bytes), len(inf1_bytes), sha_digest
        )
        blob = header + inf1_bytes
        out_infp.write_bytes(blob)
        return {
            "version": INFP_VERSION_1,
            "raw_json_bytes": raw_len,
            "col_bytes": len(col_bytes),
            "inf1_bytes": len(inf1_bytes),
            "infp_bytes": len(blob),
            "num_chunks": 1,
            "hot_macro_count": 0,
            "sha256": sha_digest.hex(),
        }

    if version == INFP_VERSION_2:
        col_bytes, hot_macros = encode_dag_v2(dag)
        chunks = [col_bytes[i : i + chunk_size] for i in range(0, len(col_bytes), chunk_size)]
        payload = bytearray()
        total_inf1 = 0
        with tempfile.TemporaryDirectory(prefix="infp_pack2_") as td:
            td_p = Path(td)
            for idx, ch in enumerate(chunks):
                inf1_ch = _ring0_compress_chunk(ch, info_bin, td_p, idx)
                total_inf1 += len(inf1_ch)
                payload.extend(INFP_CHUNK_HEADER.pack(len(ch), len(inf1_ch)))
                payload.extend(inf1_ch)
        header = INFP_V2_HEADER.pack(
            INFP_MAGIC, INFP_VERSION_2, 0, len(chunks), len(col_bytes), sha_digest
        )
        blob = header + bytes(payload)
        out_infp.write_bytes(blob)
        return {
            "version": INFP_VERSION_2,
            "raw_json_bytes": raw_len,
            "col_bytes": len(col_bytes),
            "inf1_bytes": total_inf1,
            "infp_bytes": len(blob),
            "num_chunks": len(chunks),
            "hot_macro_count": hot_macros,
            "sha256": sha_digest.hex(),
        }

    raise ValueError(f"Unsupported .infp version: {version}")


def _ring0_decomp_chunk(inf1_bytes: bytes, expected_raw_len: int, decomp_bin: Path, tmp_dir: Path, idx: int) -> bytes:
    p_inf = tmp_dir / f"chunk_{idx}.inf"
    p_raw = tmp_dir / f"chunk_{idx}.col"
    p_inf.write_bytes(inf1_bytes)
    res = subprocess.run(
        [str(decomp_bin), str(p_inf), str(p_raw)],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        raise RuntimeError(f"info_decomp failed on chunk {idx} (rc={res.returncode}): {res.stderr.strip()}")
    raw_chunk = p_raw.read_bytes()
    if len(raw_chunk) != expected_raw_len:
        raise ValueError(f"Chunk {idx} decoded size {len(raw_chunk)} != header {expected_raw_len}")
    return raw_chunk


def unpack_infp_to_dag(
    in_infp: Path,
    decomp_bin: Path = DEFAULT_DECOMP_BIN,
) -> Tuple[Dict[str, Any], str]:
    """Unpack `.infp` v1/v2 via standalone `./build/info_decomp` and verify bit-exact SHA-256."""
    if not decomp_bin.is_file():
        raise FileNotFoundError(f"Missing standalone decompressor: {decomp_bin}")
    blob = in_infp.read_bytes()
    if len(blob) < 8:
        raise ValueError(f"Truncated .infp file ({len(blob)} bytes)")

    magic, version = struct.unpack_from("<4sH", blob, 0)
    if magic != INFP_MAGIC:
        raise ValueError(f"Invalid .infp magic: {magic!r}")

    if version == INFP_VERSION_1:
        if len(blob) < INFP_V1_HEADER.size:
            raise ValueError(f"Truncated .infp v1 header ({len(blob)} bytes)")
        _, _, flags, raw_col_len, inf1_len, expected_sha = INFP_V1_HEADER.unpack(
            blob[: INFP_V1_HEADER.size]
        )
        if flags != 0 or len(blob) != INFP_V1_HEADER.size + inf1_len:
            raise ValueError("Invalid .infp v1 header/length")
        with tempfile.TemporaryDirectory(prefix="infp_unpack1_") as td:
            col_bytes = _ring0_decomp_chunk(
                blob[INFP_V1_HEADER.size :], raw_col_len, decomp_bin, Path(td), 0
            )
        dag = decode_dag_columnar(col_bytes)
    elif version == INFP_VERSION_2:
        if len(blob) < INFP_V2_HEADER.size:
            raise ValueError(f"Truncated .infp v2 header ({len(blob)} bytes)")
        _, _, flags, num_chunks, raw_col_len, expected_sha = INFP_V2_HEADER.unpack(
            blob[: INFP_V2_HEADER.size]
        )
        if flags != 0 or num_chunks == 0:
            raise ValueError(f"Invalid .infp v2 flags={flags} chunks={num_chunks}")
        off = INFP_V2_HEADER.size
        col_buf = bytearray()
        with tempfile.TemporaryDirectory(prefix="infp_unpack2_") as td:
            td_p = Path(td)
            for idx in range(num_chunks):
                if off + INFP_CHUNK_HEADER.size > len(blob):
                    raise ValueError(f"Truncated chunk {idx} header")
                ch_raw_len, ch_inf1_len = INFP_CHUNK_HEADER.unpack_from(blob, off)
                off += INFP_CHUNK_HEADER.size
                if off + ch_inf1_len > len(blob):
                    raise ValueError(f"Truncated chunk {idx} payload")
                ch_raw = _ring0_decomp_chunk(
                    blob[off : off + ch_inf1_len], ch_raw_len, decomp_bin, td_p, idx
                )
                off += ch_inf1_len
                col_buf.extend(ch_raw)
        if off != len(blob):
            raise ValueError(f"Trailing bytes after chunks: {off} != {len(blob)}")
        if len(col_buf) != raw_col_len:
            raise ValueError(f"Decoded v2 columnar size {len(col_buf)} != header {raw_col_len}")
        dag = decode_dag_v2(bytes(col_buf))
    else:
        raise ValueError(f"Unsupported .infp version: {version}")

    actual_sha = canonical_dag_sha256(dag)
    if actual_sha != expected_sha:
        raise ValueError(
            f"SHA-256 mismatch on .infp decode: expected {expected_sha.hex()}, got {actual_sha.hex()}"
        )
    return dag, actual_sha.hex()


def _strip_lean_comments(text: str) -> List[str]:
    """Strip `--` line comments and nested `/- ... -/` block comments from Lean source."""
    out_lines: List[str] = []
    block_depth = 0
    for ln in text.splitlines():
        buf: List[str] = []
        i = 0
        n = len(ln)
        in_str = False
        while i < n:
            if block_depth > 0:
                if i + 1 < n and ln[i] == "/" and ln[i + 1] == "-":
                    block_depth += 1
                    i += 2
                elif i + 1 < n and ln[i] == "-" and ln[i + 1] == "/":
                    block_depth -= 1
                    i += 2
                else:
                    i += 1
            elif in_str:
                ch = ln[i]
                buf.append(ch)
                if ch == "\\" and i + 1 < n:
                    buf.append(ln[i + 1])
                    i += 2
                elif ch == '"':
                    in_str = False
                    i += 1
                else:
                    i += 1
            else:
                if i + 1 < n and ln[i] == "-" and ln[i + 1] == "-":
                    break
                elif i + 1 < n and ln[i] == "/" and ln[i + 1] == "-":
                    block_depth += 1
                    i += 2
                else:
                    ch = ln[i]
                    buf.append(ch)
                    if ch == '"':
                        in_str = True
                    i += 1
        out_lines.append("".join(buf))
    return out_lines


def check_challenge_tcb_hygiene(challenge_src: Path, forbidden_imports: Sequence[str] = ()) -> None:
    """Verify isolated Challenge/Statements file sets no global simp/instance/option tuning."""
    lines = _strip_lean_comments(challenge_src.read_text(encoding="utf-8"))
    for idx, ln in enumerate(lines, 1):
        st = ln.strip()
        if not st:
            continue
        if re.search(r"\battribute\s*\[[^\]]*\b(instance|simp)\b", st):
            raise ValueError(f"TCB hygiene violation at {challenge_src}:{idx}: {st}")
        if re.match(r"^set_option\b", st):
            raise ValueError(f"TCB hygiene violation (set_option) at {challenge_src}:{idx}: {st}")
        m_imp = re.match(r"^import\s+(\S+)", st)
        if m_imp:
            imp = m_imp.group(1)
            for forb in forbidden_imports:
                if imp == forb or imp.startswith(forb + ".") or imp.endswith("." + forb):
                    raise ValueError(f"TCB hygiene violation (forbidden import '{imp}') at {challenge_src}:{idx}")


def verify_infp_contract(
    infp_path: Path,
    contract_path: Path,
    base_modules: str,
    search_paths: Sequence[str] = (),
    challenge_source: Optional[Path] = None,
    decomp_bin: Path = DEFAULT_DECOMP_BIN,
    lean_bin: Optional[Path] = None,
) -> Dict[str, Any]:
    """Unpack .infp via info_decomp, enforce Challenge TCB hygiene, and verify kernel contract."""
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if challenge_source is not None:
        check_challenge_tcb_hygiene(challenge_source, contract.get("forbidden_imports", ()))

    dag, sha_hex = unpack_infp_to_dag(infp_path, decomp_bin)
    lean_exe = str(lean_bin) if lean_bin is not None else (shutil.which("lean") or str(Path.home() / ".elan" / "bin" / "lean"))
    exporter = ROOT / "tools" / "lean_expr_export.lean"
    sp_list = [s for s in search_paths if s]
    sp_str = ":".join(sp_list)

    with tempfile.TemporaryDirectory(prefix="infp_contract_") as td:
        tmp_json = Path(td) / "decoded.dag.json"
        tmp_json.write_bytes(canonical_dag_bytes(dag))
        cmd = [lean_exe, "--run", str(exporter), "verify-contract", str(tmp_json), str(contract_path), base_modules]
        if sp_str:
            cmd.append(sp_str)
        env = dict(os.environ)
        env["LEAN_PATH"] = sp_str
        res = subprocess.run(cmd, cwd=str(ROOT), env=env, capture_output=True, text=True, check=False)
        if res.returncode != 0 or "CONTRACT PASS" not in res.stdout:
            raise RuntimeError(f"Contract verification failed:\n{res.stdout}\n{res.stderr}")
    return {"sha256": sha_hex, "output": res.stdout.strip()}


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="INFO .infp Proof-DAG binary container codec (v1 & v2)")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_pack = sub.add_parser("pack", help="Pack export-dag JSON into .infp")
    p_pack.add_argument("dag_json", type=Path)
    p_pack.add_argument("out_infp", type=Path)
    p_pack.add_argument("--version", type=int, choices=(1, 2), default=2)
    p_pack.add_argument("--chunk-size", type=int, default=DEFAULT_CHUNK_SIZE)
    p_pack.add_argument("--info-bin", type=Path, default=DEFAULT_INFO_BIN)

    p_unpack = sub.add_parser("unpack", help="Unpack .infp via info_decomp and verify SHA-256")
    p_unpack.add_argument("in_infp", type=Path)
    p_unpack.add_argument("out_json", type=Path)
    p_unpack.add_argument("--decomp-bin", type=Path, default=DEFAULT_DECOMP_BIN)

    p_bench = sub.add_parser("bench", help="Roundtrip pack + info_decomp unpack benchmark")
    p_bench.add_argument("dag_json", type=Path)
    p_bench.add_argument("--version", type=int, choices=(1, 2), default=2)
    p_bench.add_argument("--chunk-size", type=int, default=DEFAULT_CHUNK_SIZE)
    p_bench.add_argument("--info-bin", type=Path, default=DEFAULT_INFO_BIN)
    p_bench.add_argument("--decomp-bin", type=Path, default=DEFAULT_DECOMP_BIN)

    p_ver = sub.add_parser("verify-contract", help="Verify .infp v2 against isolated Challenge contract")
    p_ver.add_argument("in_infp", type=Path)
    p_ver.add_argument("contract_json", type=Path)
    p_ver.add_argument("--base-modules", default="Init")
    p_ver.add_argument("--lean-path", default="")
    p_ver.add_argument("--challenge-source", type=Path, default=None)
    p_ver.add_argument("--decomp-bin", type=Path, default=DEFAULT_DECOMP_BIN)

    args = parser.parse_args(argv)
    if args.cmd == "pack":
        raw_text = args.dag_json.read_bytes()
        dag = json.loads(raw_text.decode("utf-8"))
        metrics = pack_dag_to_infp(
            dag, args.out_infp, args.info_bin, len(raw_text), version=args.version, chunk_size=args.chunk_size
        )
        print(json.dumps(metrics, indent=2))
        return 0
    if args.cmd == "unpack":
        dag, sha_hex = unpack_infp_to_dag(args.in_infp, args.decomp_bin)
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_bytes(canonical_dag_bytes(dag))
        print(json.dumps({"sha256": sha_hex, "stats": dag["stats"]}, indent=2))
        return 0
    if args.cmd == "bench":
        raw_text = args.dag_json.read_bytes()
        dag = json.loads(raw_text.decode("utf-8"))
        orig_sha = canonical_dag_sha256(dag).hex()
        with tempfile.TemporaryDirectory(prefix="infp_bench_") as td:
            out_infp = Path(td) / "bench.infp"
            metrics = pack_dag_to_infp(
                dag, out_infp, args.info_bin, len(raw_text), version=args.version, chunk_size=args.chunk_size
            )
            decoded_dag, decoded_sha = unpack_infp_to_dag(out_infp, args.decomp_bin)
            assert decoded_sha == orig_sha
            assert decoded_dag["stats"] == dag["stats"]
            metrics["verified_sha256"] = decoded_sha
            metrics["ratio_vs_json"] = round(len(raw_text) / metrics["infp_bytes"], 3)
            print(json.dumps(metrics, indent=2))
        return 0
    if args.cmd == "verify-contract":
        sp = [s for s in args.lean_path.split(":") if s]
        res = verify_infp_contract(
            args.in_infp,
            args.contract_json,
            args.base_modules,
            search_paths=sp,
            challenge_source=args.challenge_source,
            decomp_bin=args.decomp_bin,
        )
        print(json.dumps(res, indent=2))
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
