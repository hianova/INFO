#!/usr/bin/env python3
"""
INFO v1.0.0 — Hutter-Style Compression & Self-Extracting Total Size Benchmark
=============================================================================
Compares zlib/deflate (-9), zstd (-19), bzip2 (-9), lzma (-9), INFO (--no-alg),
INFO (payload), and INFO Hutter Total (payload + standalone build/info_decomp) across:
  - docs_real       (64 KB English technical Markdown & stdlib prose)
  - code_real       (64 KB C17 source code from INFO)
  - py_stdlib       (64 KB Python standard-library source)
  - fsmx_exact      (64 KB depth-2 FSMX Markov source with analytical H*)
  - alg_lfsr23      (64 KB 23-bit non-cycling LFSR)
  - alg_ca32_rule30 (64 KB 32-bit periodic CA Rule-30)
  - alg_affine16    (64 KB mod-65536 linear congruential stream)
plus optional `--enwik <path>` slice evaluation.
"""

from __future__ import annotations

import argparse
import bz2
import hashlib
import inspect
import lzma
import math
import shutil
import subprocess
import sys
import tempfile
import zlib
from pathlib import Path
from typing import Dict, List, Optional, Tuple


ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
INFO_BIN = BUILD / "info"
DECOMP_BIN = BUILD / "info_decomp"
CORPUS_SIZE = 65536
CLI_MAX_BYTES = 4 * 1024 * 1024


def py_gen_lfsr23(init_state: int, nbytes: int) -> bytes:
    s = init_state & 0x7FFFFF
    if s == 0:
        s = 0x5ACE1
    out = bytearray(nbytes)
    for i in range(nbytes):
        bv = 0
        for _ in range(8):
            nxt = ((s >> 0) ^ (s >> 5)) & 1
            s = ((s >> 1) | (nxt << 22)) & 0x7FFFFF
            bv = (bv << 1) | nxt
        out[i] = bv
    return bytes(out)


def py_gen_ca32_rule30(init_row: int, nbytes: int) -> bytes:
    row = init_row & 0xFFFFFFFF
    out = bytearray(nbytes)
    for i in range(0, nbytes, 4):
        nxt = 0
        for b in range(32):
            rb = 31 if b == 0 else b - 1
            lb = 0 if b == 31 else b + 1
            l = (row >> lb) & 1
            c = (row >> b) & 1
            r = (row >> rb) & 1
            if l ^ (c | r):
                nxt |= 1 << b
        row = nxt
        for sub in range(4):
            if i + sub < nbytes:
                out[i + sub] = (row >> ((3 - sub) * 8)) & 0xFF
    return bytes(out)


def py_gen_affine16(a: int, c: int, x0: int, nbytes: int) -> bytes:
    x = x0 & 0xFFFF
    mul = (a & 0xFFFC) | 1
    inc = c | 1
    out = bytearray(nbytes)
    for i in range(0, nbytes, 2):
        x = (mul * x + inc) & 0xFFFF
        out[i] = (x >> 8) & 0xFF
        if i + 1 < nbytes:
            out[i + 1] = x & 0xFF
    return bytes(out)


def build_docs_real(target_bytes: int = CORPUS_SIZE) -> bytes:
    chunks: List[bytes] = []
    md_roots = [ROOT, ROOT.parent / "FLOW"]
    seen: set[Path] = set()
    for base in md_roots:
        if base.is_dir():
            for p in sorted(base.rglob("*.md")):
                if "build" in p.parts or ".git" in p.parts:
                    continue
                rp = p.resolve()
                if rp not in seen:
                    seen.add(rp)
                    chunks.append(p.read_bytes())
    for sibling in ["SOUND", "PHY"]:
        sp = ROOT.parent / sibling / "README.md"
        if sp.is_file() and sp.resolve() not in seen:
            seen.add(sp.resolve())
            chunks.append(sp.read_bytes())
    blob = b"\n".join(chunks)
    if len(blob) < target_bytes:
        import collections
        import email
        import json
        import logging
        import pathlib
        import re
        import unittest
        import urllib
        import argparse as _ap
        import difflib as _df

        extra: List[str] = []
        for mod in [_ap, _df, collections, email, urllib, logging, unittest, pathlib, re, json]:
            doc = inspect.getdoc(mod)
            if doc:
                extra.append(doc)
            for _, obj in inspect.getmembers(mod):
                d = inspect.getdoc(obj)
                if d:
                    extra.append(d)
        blob = blob + b"\n" + "\n".join(extra).encode("utf-8", errors="ignore")
    assert len(blob) >= target_bytes, f"docs_real too short: {len(blob)}"
    return blob[:target_bytes]


def build_code_real(target_bytes: int = CORPUS_SIZE) -> bytes:
    parts = [
        (ROOT / "src" / "info_ring0.c").read_bytes(),
        (ROOT / "include" / "info.h").read_bytes(),
        (ROOT / "src" / "info_cli.c").read_bytes(),
    ]
    blob = b"\n".join(parts)
    assert len(blob) >= target_bytes, f"code_real too short: {len(blob)}"
    return blob[:target_bytes]


def build_py_stdlib(target_bytes: int = CORPUS_SIZE) -> bytes:
    import difflib
    import json.decoder

    parts: List[bytes] = []
    for mod in [argparse, difflib, inspect, json.decoder]:
        parts.append(Path(inspect.getfile(mod)).read_bytes())
    blob = b"\n".join(parts)
    assert len(blob) >= target_bytes, f"py_stdlib too short: {len(blob)}"
    return blob[:target_bytes]


def build_fsmx_exact(target_bytes: int = CORPUS_SIZE) -> Tuple[bytes, float]:
    """Depth-2 binary Markov source with exact analytical entropy rate H* (bpb)."""
    p1 = [0.12, 0.86, 0.22, 0.78]  # state s = (b_{t-2} << 1) | b_{t-1}
    # Stationary distribution of 4x4 chain via power iteration to machine precision
    pi = [0.25, 0.25, 0.25, 0.25]
    for _ in range(256):
        nxt = [0.0] * 4
        for s in range(4):
            q1 = p1[s]
            q0 = 1.0 - q1
            nxt[((s << 1) & 3) | 0] += pi[s] * q0
            nxt[((s << 1) & 3) | 1] += pi[s] * q1
        pi = nxt
    h_bit = 0.0
    for s in range(4):
        q1 = p1[s]
        q0 = 1.0 - q1
        hb = -(q1 * math.log2(q1) + q0 * math.log2(q0))
        h_bit += pi[s] * hb
    h_byte = h_bit * 8.0

    # Deterministic LCG to sample bit stream cleanly
    rng = 0x5EED123498765432
    state = 0
    out = bytearray(target_bytes)
    for i in range(target_bytes):
        bv = 0
        for _ in range(8):
            rng = (rng * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
            u = (rng >> 32) / float(1 << 32)
            bit = 1 if u < p1[state] else 0
            bv = (bv << 1) | bit
            state = ((state << 1) & 3) | bit
        out[i] = bv
    return bytes(out), h_byte


def compress_zstd19(raw_path: Path, zst_path: Path) -> int:
    zstd_bin = shutil.which("zstd")
    assert zstd_bin is not None, "zstd CLI not found on PATH"
    res = subprocess.run(
        [zstd_bin, "-19", "-q", "-f", str(raw_path), "-o", str(zst_path)],
        capture_output=True,
        text=True,
        check=False,
    )
    assert res.returncode == 0, f"zstd failed: {res.stderr}"
    return zst_path.stat().st_size


def compress_info(
    raw_path: Path, inf_path: Path, extra_flags: Optional[List[str]] = None
) -> Tuple[int, str]:
    cmd = [str(INFO_BIN), "compress", str(raw_path), str(inf_path)]
    if extra_flags:
        cmd.extend(extra_flags)
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    assert res.returncode == 0, f"info compress failed: {res.stderr}"
    return inf_path.stat().st_size, res.stdout.strip()


def decomp_verify_sha256(inf_path: Path, rec_path: Path, orig_sha256: str, label: str) -> None:
    res = subprocess.run(
        [str(DECOMP_BIN), str(inf_path), str(rec_path)],
        capture_output=True,
        text=True,
        check=False,
    )
    assert res.returncode == 0, f"info_decomp failed on {label}: {res.stderr}"
    got = hashlib.sha256(rec_path.read_bytes()).hexdigest()
    assert got == orig_sha256, f"SHA-256 mismatch on {label}: {got} != {orig_sha256}"


def bench_corpus(
    name: str, data: bytes, decomp_size: int, tdir: Path, h_star_bpb: Optional[float] = None
) -> Dict[str, float]:
    n = len(data)
    raw_p = tdir / f"{name}.bin"
    raw_p.write_bytes(data)
    sha = hashlib.sha256(data).hexdigest()

    deflate_sz = len(zlib.compress(data, level=9))
    zst_sz = compress_zstd19(raw_p, tdir / f"{name}.zst")
    bzip2_sz = len(bz2.compress(data, compresslevel=9))
    lzma_sz = len(lzma.compress(data, preset=9))

    noalg_inf = tdir / f"{name}_noalg.inf"
    noalg_sz, _ = compress_info(raw_p, noalg_inf, ["--no-alg"])
    decomp_verify_sha256(noalg_inf, tdir / f"{name}_noalg.rec", sha, f"{name}(no-alg)")

    info_inf = tdir / f"{name}.inf"
    info_sz, _ = compress_info(raw_p, info_inf)
    decomp_verify_sha256(info_inf, tdir / f"{name}.rec", sha, name)

    hutter_total = info_sz + decomp_size

    def bpb(sz: int) -> float:
        return (sz * 8.0) / float(n)

    row = {
        "n": float(n),
        "deflate_bpb": bpb(deflate_sz),
        "zstd_bpb": bpb(zst_sz),
        "bzip2_bpb": bpb(bzip2_sz),
        "lzma_bpb": bpb(lzma_sz),
        "noalg_bpb": bpb(noalg_sz),
        "info_bpb": bpb(info_sz),
        "hutter_bpb": bpb(hutter_total),
        "deflate_sz": float(deflate_sz),
        "zstd_sz": float(zst_sz),
        "bzip2_sz": float(bzip2_sz),
        "lzma_sz": float(lzma_sz),
        "info_sz": float(info_sz),
        "hutter_sz": float(hutter_total),
        "h_star": h_star_bpb if h_star_bpb is not None else -1.0,
    }
    return row


def main() -> int:
    parser = argparse.ArgumentParser(description="INFO v1.0.0 Hutter Compression Benchmark")
    parser.add_argument("--enwik", type=Path, default=None, help="Optional path to enwik8/enwik9")
    args = parser.parse_args()

    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}"
    assert DECOMP_BIN.is_file(), f"Missing {DECOMP_BIN}"
    decomp_size = DECOMP_BIN.stat().st_size

    fsmx_data, fsmx_hstar = build_fsmx_exact(CORPUS_SIZE)
    corpora: List[Tuple[str, bytes, Optional[float]]] = [
        ("docs_real", build_docs_real(CORPUS_SIZE), None),
        ("code_real", build_code_real(CORPUS_SIZE), None),
        ("py_stdlib", build_py_stdlib(CORPUS_SIZE), None),
        ("fsmx_exact", fsmx_data, fsmx_hstar),
        ("alg_lfsr23", py_gen_lfsr23(0x5ACE1, CORPUS_SIZE), None),
        ("alg_ca32_rule30", py_gen_ca32_rule30(0x13579BDF, CORPUS_SIZE), None),
        ("alg_affine16", py_gen_affine16(25173, 13849, 7, CORPUS_SIZE), None),
    ]

    if args.enwik is not None:
        assert args.enwik.is_file(), f"Missing --enwik file: {args.enwik}"
        raw_enwik = args.enwik.read_bytes()[:CLI_MAX_BYTES]
        corpora.append((f"enwik_{len(raw_enwik)}", raw_enwik, None))

    print(
        f"[Experiment 1] INFO v1.0.0 Hutter Compression Benchmark "
        f"(standalone decomp={decomp_size} B, SHA-256 verified)"
    )
    header = (
        f"  {'Corpus':<16} | {'Size':>7} | {'deflate-9':>9} | {'zstd-19':>8} | "
        f"{'bzip2-9':>8} | {'lzma-9':>8} | {'INFO':>7} | {'HutterTot':>9} | {'Notes':<18}"
    )
    print(header)
    print("  " + "-" * (len(header) - 2))

    results: Dict[str, Dict[str, float]] = {}
    with tempfile.TemporaryDirectory(prefix="info_hutter_") as td:
        tdir = Path(td)
        for name, data, h_star in corpora:
            r = bench_corpus(name, data, decomp_size, tdir, h_star)
            results[name] = r
            note = f"H*={h_star:.3f}" if h_star is not None else "SHA256 OK"
            if name.startswith("alg_"):
                note = f"noalg={r['noalg_bpb']:.3f}"
            print(
                f"  {name:<16} | {int(r['n']):>7} | {r['deflate_bpb']:>9.3f} | "
                f"{r['zstd_bpb']:>8.3f} | {r['bzip2_bpb']:>8.3f} | {r['lzma_bpb']:>8.3f} | "
                f"{r['info_bpb']:>7.3f} | {int(r['hutter_sz']):>8}B | {note:<18}"
            )

    # Assertions matching Gate / Plan criteria
    for real_name in ["docs_real", "code_real", "py_stdlib"]:
        r = results[real_name]
        assert r["info_bpb"] < r["deflate_bpb"], f"{real_name}: INFO >= deflate-9"
        assert r["info_bpb"] < r["zstd_bpb"], f"{real_name}: INFO >= zstd-19"
        assert r["info_bpb"] < r["bzip2_bpb"], f"{real_name}: INFO >= bzip2-9"

    r_fsmx = results["fsmx_exact"]
    assert r_fsmx["info_bpb"] < r_fsmx["deflate_bpb"], "fsmx_exact: INFO >= deflate-9"
    assert r_fsmx["info_bpb"] - r_fsmx["h_star"] < 0.35, (
        f"fsmx_exact redundancy too large: info={r_fsmx['info_bpb']:.3f} vs H*={r_fsmx['h_star']:.3f}"
    )

    for alg_name in ["alg_lfsr23", "alg_ca32_rule30", "alg_affine16"]:
        r = results[alg_name]
        for base in ["deflate_bpb", "zstd_bpb", "bzip2_bpb", "lzma_bpb"]:
            min_thresh = 7.3 if (alg_name == "alg_affine16" and base == "bzip2_bpb") else 7.5
            assert r[base] > min_thresh, (
                f"{alg_name}: expected baseline {base} > {min_thresh}, got {r[base]:.3f}"
            )
        assert r["info_bpb"] < 0.15, f"{alg_name}: INFO {r['info_bpb']:.3f} >= 0.15 bpb"
        min_base_sz = min(r["deflate_sz"], r["zstd_sz"], r["bzip2_sz"], r["lzma_sz"])
        assert r["hutter_sz"] < min_base_sz, (
            f"{alg_name}: HutterTotal {r['hutter_sz']} >= baseline payload {min_base_sz}"
        )

    print("  [PASS] All real-corpus wins, analytical H* tracking, HutterTotal wins, and SHA-256 checks verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
