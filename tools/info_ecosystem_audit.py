#!/usr/bin/env python3
"""
INFO v1.0.0 — FLOW Ecosystem Structural MDL Auditor
=====================================================
Uses INFO's Ring-0 α-canonicalizer (`build/info alpha-canon`), α-NCD/MI
evaluator (`build/info alpha-ncd`), and Joint MDL extractor
(`build/info eval-mdl-group`) to detect structurally isomorphic files and
functions across FLOW and domain repositories, quantify real ΔMDL refactoring
benefits, and prioritize abstractions to promote into FLOW.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple


ROOT = Path(__file__).resolve().parent.parent
INFO_BIN = ROOT / "build" / "info"

EXT_TO_LANG = {
    ".c": "c",
    ".h": "c",
    ".lean": "lean",
    ".py": "py",
}
SKIP_DIRS = {"build", ".git", "assets", "data", "__pycache__", ".elan", "node_modules"}
MIN_FILE_BYTES = 256
MAX_FILE_BYTES = 512 * 1024


def run_info(args: List[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(INFO_BIN), *args],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
        check=False,
    )


def discover_files(roots: Sequence[Path]) -> List[Dict[str, object]]:
    files: List[Dict[str, object]] = []
    seen_real: Set[Path] = set()
    for root in roots:
        if not root.is_dir():
            continue
        r_res = root.resolve()
        repo = r_res.name
        for p in sorted(r_res.rglob("*")):
            if not p.is_file():
                continue
            if any(part in SKIP_DIRS for part in p.parts):
                continue
            if p.name.endswith("_schema_abi.h"):
                continue
            lang = EXT_TO_LANG.get(p.suffix)
            if lang is None:
                continue
            rp = p.resolve()
            if rp in seen_real:
                continue
            sz = rp.stat().st_size
            if sz < MIN_FILE_BYTES or sz > MAX_FILE_BYTES:
                continue
            seen_real.add(rp)
            rel = p.relative_to(r_res).as_posix()
            files.append(
                {
                    "idx": len(files),
                    "repo": repo,
                    "lang": lang,
                    "path": rp,
                    "label": f"{repo}/{rel}",
                    "raw_bytes": sz,
                }
            )
    return files


def shingles_from_text(text: str, k: int = 5) -> Set[int]:
    # Collapse global per-file De Bruijn IDs only during shingle pre-filtering so
    # shared libraries buried at different file offsets still surface for exact Ring-0 alpha-ncd.
    folded = re.sub(r"\bV(?:[0-9A-F]{2}|X)\b", "ID", text)
    toks = re.findall(r"[A-Za-z0-9_']+|[{}()\[\];:,=<>!+\-*/&|^~]+", folded)
    if len(toks) < k:
        return {hash(tuple(toks))} if toks else set()
    return {hash(tuple(toks[i : i + k])) for i in range(len(toks) - k + 1)}


def rough_skeleton_shingles(text: str, k: int = 4) -> Set[int]:
    # Lightweight structural tokenizer purely for pre-filtering function candidates
    # before invoking Ring-0 `info alpha-canon` and `info alpha-ncd`.
    cleaned = re.sub(r"//[^\n]*|--[^\n]*|#[^\n]*", "", text)
    cleaned = re.sub(r"/\*[\s\S]*?\*/|/-[\s\S]*?-/", "", cleaned)
    cleaned = re.sub(r'"[^"\n]*"', " STR ", cleaned)
    toks = re.findall(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+|[{}()\[\];:,=<>!+\-*/&|^~]+", cleaned)
    kw = {
        "if", "else", "for", "while", "return", "switch", "case", "struct", "typedef",
        "static", "const", "uint32_t", "uint64_t", "size_t", "int64_t", "def", "theorem",
        "lemma", "structure", "by", "let", "have", "class", "import", "in", "match",
        "with", "omega", "bv_decide",
    }
    norm = [t if (t in kw or t.startswith(("flow_", "FLOW_", "searu_", "SEARU_", "Flow")) or not t[0].isalpha()) else "ID" for t in toks]
    if len(norm) < k:
        return {hash(tuple(norm))} if norm else set()
    return {hash(tuple(norm[i : i + k])) for i in range(len(norm) - k + 1)}


def jaccard(a: Set[int], b: Set[int]) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    if inter == 0:
        return 0.0
    return inter / float(len(a | b))


def canonicalize_all(files: List[Dict[str, object]], tmp_dir: Path) -> None:
    cdir = tmp_dir / "canon"
    cdir.mkdir(parents=True, exist_ok=True)

    def _one(entry: Dict[str, object]) -> None:
        cpath = cdir / f"f_{entry['idx']}.canon"
        res = run_info(
            ["alpha-canon", str(entry["path"]), str(cpath), "--lang", str(entry["lang"])]
        )
        assert res.returncode == 0, f"alpha-canon failed on {entry['label']}: {res.stderr}"
        ctext = cpath.read_text(encoding="utf-8", errors="ignore")
        entry["canon_path"] = cpath
        entry["canon_text"] = ctext
        entry["canon_lines"] = [ln for ln in ctext.splitlines() if ln.strip()]
        entry["shingles"] = shingles_from_text(ctext, k=5)

    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        list(ex.map(_one, files))


def eval_alpha_ncd_pair(
    pa: Path, pb: Path, lang: str, out_json: Path
) -> Dict[str, float]:
    res = run_info(
        ["alpha-ncd", str(pa), str(pb), "--lang", lang, "--out-json", str(out_json)]
    )
    assert res.returncode == 0, f"alpha-ncd failed ({pa.name}, {pb.name}): {res.stderr}"
    j = json.loads(out_json.read_text(encoding="utf-8"))
    q12_b = 4096.0 * 8.0
    rla = max(1e-9, j["raw_la_q12"] / q12_b)
    rlb = max(1e-9, j["raw_lb_q12"] / q12_b)
    rlba = j["raw_lba_q12"] / q12_b
    rlab = j["raw_lab_q12"] / q12_b
    ala = max(1e-9, j["alpha_la_q12"] / q12_b)
    alb = max(1e-9, j["alpha_lb_q12"] / q12_b)
    alba = j["alpha_lba_q12"] / q12_b
    alab = j["alpha_lab_q12"] / q12_b

    raw_ncd = max(0.0, (min(rla + rlba, rlb + rlab) - min(rla, rlb)) / max(rla, rlb))
    alpha_ncd = max(0.0, (min(ala + alba, alb + alab) - min(ala, alb)) / max(ala, alb))
    mi_ba = max(0.0, alb - alba)
    mi_ab = max(0.0, ala - alab)
    mi_alpha = 0.5 * (mi_ba + mi_ab)
    redund_pct = max(mi_ba / alb, mi_ab / ala) * 100.0
    return {
        "raw_ncd": raw_ncd,
        "alpha_ncd": alpha_ncd,
        "alpha_la_bytes": ala,
        "alpha_lb_bytes": alb,
        "alpha_lba_bytes": alba,
        "alpha_lab_bytes": alab,
        "mi_alpha_bytes": mi_alpha,
        "redund_alpha_pct": redund_pct,
        "subsume": "A->B" if alba < alab else "B->A",
    }


def analyze_file_pairs(
    files: List[Dict[str, object]], tmp_dir: Path, max_eval: int
) -> List[Dict[str, object]]:
    cands: List[Tuple[float, int, int]] = []
    n = len(files)
    for i in range(n):
        fi = files[i]
        for j in range(i + 1, n):
            fj = files[j]
            if fi["repo"] == fj["repo"] or fi["lang"] != fj["lang"]:
                continue
            jac = jaccard(fi["shingles"], fj["shingles"])  # type: ignore[arg-type]
            if jac >= 0.08:
                cands.append((jac, i, j))
    cands.sort(key=lambda x: (-x[0], x[1], x[2]))
    cands = cands[:max_eval]

    pdir = tmp_dir / "file_ncd"
    pdir.mkdir(parents=True, exist_ok=True)

    def _eval(item: Tuple[int, Tuple[float, int, int]]) -> Dict[str, object]:
        k, (jac, i, j) = item
        fi, fj = files[i], files[j]
        metrics = eval_alpha_ncd_pair(
            fi["path"],  # type: ignore[arg-type]
            fj["path"],  # type: ignore[arg-type]
            str(fi["lang"]),
            pdir / f"pair_{k}.json",
        )
        return {
            "i": i,
            "j": j,
            "a": fi["label"],
            "b": fj["label"],
            "repo_a": fi["repo"],
            "repo_b": fj["repo"],
            "lang": fi["lang"],
            "jaccard": jac,
            **metrics,
        }

    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        results = list(ex.map(_eval, enumerate(cands)))
    results.sort(key=lambda r: (float(r["alpha_ncd"]), -float(r["mi_alpha_bytes"])))
    return results


def extract_blocks_from_file(entry: Dict[str, object]) -> List[Dict[str, object]]:
    lang = str(entry["lang"])
    text = Path(entry["path"]).read_text(encoding="utf-8", errors="ignore")  # type: ignore[arg-type]
    lines = text.splitlines()
    blocks: List[Dict[str, object]] = []

    if lang == "py":
        i = 0
        while i < len(lines):
            if re.match(r"^(def|class)\s+([A-Za-z_][A-Za-z0-9_]*)", lines[i]):
                start = i
                name = lines[i].split("(")[0].split(":")[0].strip()
                i += 1
                while i < len(lines):
                    if lines[i].strip() != "" and not lines[i].startswith((" ", "\t")):
                        break
                    i += 1
                end = i
                while end > start + 1 and lines[end - 1].strip() == "":
                    end -= 1
                body = "\n".join(lines[start:end])
                if (end - start) >= 12 and len(body) >= 180:
                    blocks.append({"name": name, "start": start + 1, "end": end, "text": body})
            else:
                i += 1
    elif lang == "lean":
        decl_rx = re.compile(
            r"^(?:private\s+|protected\s+)?(?:theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_'.]+)"
        )
        i = 0
        while i < len(lines):
            m = decl_rx.match(lines[i])
            if m:
                start = i
                name = m.group(1)
                i += 1
                while i < len(lines):
                    if decl_rx.match(lines[i]) or re.match(
                        r"^(?:/-!|namespace|end\s|section|#|@\[)", lines[i]
                    ):
                        break
                    i += 1
                end = i
                while end > start + 1 and lines[end - 1].strip() == "":
                    end -= 1
                body = "\n".join(lines[start:end])
                if (end - start) >= 12 and len(body) >= 180:
                    blocks.append({"name": name, "start": start + 1, "end": end, "text": body})
            else:
                i += 1
    elif lang == "c":
        i = 0
        while i < len(lines):
            ln = lines[i]
            if (
                not ln.startswith((" ", "\t", "#", "/", "*", "}"))
                and "(" in ln
                and not ln.strip().endswith(";")
            ):
                start = i
                depth = 0
                saw_brace = False
                j = i
                while j < len(lines):
                    for ch in lines[j]:
                        if ch == "{":
                            depth += 1
                            saw_brace = True
                        elif ch == "}":
                            depth -= 1
                    j += 1
                    if saw_brace and depth <= 0:
                        break
                    if not saw_brace and (j - start) > 6:
                        break
                if saw_brace and depth == 0 and (j - start) >= 12:
                    body = "\n".join(lines[start:j])
                    if len(body) >= 180 and "typedef struct" not in lines[start]:
                        sig = lines[start].split("(")[0].strip().split()[-1].lstrip("*")
                        blocks.append({"name": sig, "start": start + 1, "end": j, "text": body})
                i = j
            else:
                i += 1

    out: List[Dict[str, object]] = []
    for b in blocks:
        sh = rough_skeleton_shingles(str(b["text"]), k=4)
        if len(sh) < 6:
            continue
        out.append(
            {
                "file_idx": entry["idx"],
                "repo": entry["repo"],
                "lang": lang,
                "label": entry["label"],
                "path": entry["path"],
                "name": b["name"],
                "start": b["start"],
                "end": b["end"],
                "text": b["text"],
                "shingles": sh,
            }
        )
    return out


def analyze_function_clones(
    files: List[Dict[str, object]], tmp_dir: Path, max_eval: int
) -> List[Dict[str, object]]:
    all_blocks: List[Dict[str, object]] = []
    for f in files:
        all_blocks.extend(extract_blocks_from_file(f))

    cands: List[Tuple[float, int, int]] = []
    nb = len(all_blocks)
    by_lang: Dict[str, List[int]] = defaultdict(list)
    for idx, b in enumerate(all_blocks):
        by_lang[str(b["lang"])].append(idx)

    for idxs in by_lang.values():
        m = len(idxs)
        for p in range(m):
            i = idxs[p]
            bi = all_blocks[i]
            for q in range(p + 1, m):
                j = idxs[q]
                bj = all_blocks[j]
                if bi["repo"] == bj["repo"]:
                    continue
                jac = jaccard(bi["shingles"], bj["shingles"])  # type: ignore[arg-type]
                if jac >= 0.22:
                    cands.append((jac, i, j))
    cands.sort(key=lambda x: (-x[0], x[1], x[2]))
    cands = cands[:max_eval]

    fdir = tmp_dir / "func_ncd"
    fdir.mkdir(parents=True, exist_ok=True)
    needed_ids = {i for _, i, j in cands} | {j for _, i, j in cands}
    block_paths: Dict[int, Path] = {}
    for bid in needed_ids:
        bp = fdir / f"blk_{bid}.src"
        bp.write_text(str(all_blocks[bid]["text"]), encoding="utf-8")
        block_paths[bid] = bp

    def _eval(item: Tuple[int, Tuple[float, int, int]]) -> Dict[str, object]:
        k, (jac, i, j) = item
        bi, bj = all_blocks[i], all_blocks[j]
        metrics = eval_alpha_ncd_pair(
            block_paths[i], block_paths[j], str(bi["lang"]), fdir / f"fn_{k}.json"
        )
        return {
            "file_idx_a": bi["file_idx"],
            "file_idx_b": bj["file_idx"],
            "span_a": f"{bi['label']}:{bi['start']}-{bi['end']} ({bi['name']})",
            "span_b": f"{bj['label']}:{bj['start']}-{bj['end']} ({bj['name']})",
            "text_a": bi["text"],
            "text_b": bj["text"],
            "lang": bi["lang"],
            "jaccard": jac,
            **metrics,
        }

    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
        res = list(ex.map(_eval, enumerate(cands)))
    res.sort(key=lambda r: (float(r["alpha_ncd"]), -float(r["mi_alpha_bytes"])))
    return res


def cluster_and_eval_joint_mdl(
    files: List[Dict[str, object]],
    pair_rows: List[Dict[str, object]],
    func_rows: List[Dict[str, object]],
    tmp_dir: Path,
) -> List[Dict[str, object]]:
    n = len(files)
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(a: int, b: int) -> None:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[rb] = ra

    active_edges: Set[Tuple[int, int]] = set()
    for row in pair_rows:
        i, j = int(row["i"]), int(row["j"])
        ancd = float(row["alpha_ncd"])
        red = float(row["redund_alpha_pct"])
        if ancd < 0.78 or red >= 26.0:
            union(i, j)
            active_edges.add((i, j))
    for fr in func_rows:
        if float(fr["alpha_ncd"]) < 0.25 or float(fr["redund_alpha_pct"]) >= 85.0:
            fi_a, fi_b = int(fr["file_idx_a"]), int(fr["file_idx_b"])
            union(fi_a, fi_b)
            active_edges.add((fi_a, fi_b))

    comps: Dict[int, Set[int]] = defaultdict(set)
    for i, j in active_edges:
        comps[find(i)].add(i)
        comps[find(j)].add(j)

    cluster_results: List[Dict[str, object]] = []
    mdir = tmp_dir / "mdl_clusters"
    mdir.mkdir(parents=True, exist_ok=True)

    for cid, raw_nodes in enumerate(comps.values()):
        nodes = sorted(raw_nodes)
        repos = {str(files[idx]["repo"]) for idx in nodes}
        if len(repos) < 2:
            continue
        if len(nodes) > 16:
            nodes = nodes[:16]
        node_set = set(nodes)
        lang = str(files[nodes[0]]["lang"])

        # Shared canonical skeleton: canonical lines occurring in >= 2 distinct repos in cluster
        line_repos: Dict[str, Set[str]] = defaultdict(set)
        ordered_lines: List[str] = []
        for idx in nodes:
            rname = str(files[idx]["repo"])
            for ln in files[idx]["canon_lines"]:  # type: ignore[attr-defined]
                s = ln.strip()
                if len(s) < 8 or s in ("{", "}", ");"):
                    continue
                if s not in line_repos:
                    ordered_lines.append(s)
                line_repos[s].add(rname)

        shared_lines = [ln for ln in ordered_lines if len(line_repos[ln]) >= 2]
        # If whole-file offsets shifted global De Bruijn IDs, distill shared skeleton
        # from the verified overlapping function blocks of this cluster.
        matched_funcs = [
            fr
            for fr in func_rows
            if int(fr["file_idx_a"]) in node_set
            and int(fr["file_idx_b"]) in node_set
            and (float(fr["alpha_ncd"]) < 0.25 or float(fr["redund_alpha_pct"]) >= 85.0)
        ]
        if matched_funcs:
            # Evaluate extracted clone-group MDL cleanly on the overlapping blocks
            blk_texts: List[str] = []
            seen_spans: Set[str] = set()
            for fr in matched_funcs[:8]:
                for k_span, k_txt in [("span_a", "text_a"), ("span_b", "text_b")]:
                    sp = str(fr[k_span])
                    if sp not in seen_spans:
                        seen_spans.add(sp)
                        blk_texts.append(str(fr[k_txt]))
            shared_src_p = mdir / f"cluster_{cid}_fn_shared.src"
            shared_src_p.write_text(str(matched_funcs[0]["text_a"]), encoding="utf-8")
            blk_paths: List[str] = []
            for bi, bt in enumerate(blk_texts):
                bp = mdir / f"cluster_{cid}_blk_{bi}.src"
                bp.write_text(bt, encoding="utf-8")
                blk_paths.append(str(bp))
            out_fn_j = mdir / f"cluster_{cid}_fn_mdl.json"
            res_fn = run_info([
                "eval-mdl-group", "--alpha", "--lang", lang,
                "--shared", str(shared_src_p), "--out-json", str(out_fn_j), *blk_paths
            ])
            if res_fn.returncode == 0:
                jm_fn = json.loads(out_fn_j.read_text(encoding="utf-8"))
                q12_b = 4096.0 * 8.0
                fn_gain = jm_fn["extract_gain_bits_q12"] / q12_b
            else:
                fn_gain = 0.0
        else:
            fn_gain = 0.0

        # Evaluate whole-file cluster MDL if common file lines exist, else use clone-block ΔMDL
        if len(shared_lines) >= 3:
            shared_p = mdir / f"cluster_{cid}_shared.canon"
            shared_p.write_text("\n".join(shared_lines) + "\n", encoding="utf-8")
            out_j = mdir / f"cluster_{cid}_mdl.json"
            member_paths = [str(files[idx]["path"]) for idx in nodes]
            res = run_info([
                "eval-mdl-group", "--alpha", "--lang", lang,
                "--shared", str(shared_p), "--out-json", str(out_j), *member_paths
            ])
            assert res.returncode == 0, f"eval-mdl-group failed on cluster {cid}: {res.stderr}"
            jm = json.loads(out_j.read_text(encoding="utf-8"))
            q12_b = 4096.0 * 8.0
            gain_b = max(fn_gain, jm["extract_gain_bits_q12"] / q12_b)
            seq_b = jm["joint_savings_bits_q12"] / q12_b
            indep_b = jm["sum_indep_bits_q12"] / q12_b
            shared_b = jm["shared_bits_q12"] / q12_b
        elif matched_funcs:
            q12_b = 4096.0 * 8.0
            jm = json.loads((mdir / f"cluster_{cid}_fn_mdl.json").read_text(encoding="utf-8"))
            gain_b = jm["extract_gain_bits_q12"] / q12_b
            seq_b = jm["joint_savings_bits_q12"] / q12_b
            indep_b = jm["sum_indep_bits_q12"] / q12_b
            shared_b = jm["shared_bits_q12"] / q12_b
            shared_lines = str(matched_funcs[0]["text_a"]).splitlines()
        else:
            continue

        root_scores: Dict[int, float] = defaultdict(float)
        for row in pair_rows:
            ri, rj = int(row["i"]), int(row["j"])
            if ri in node_set and rj in node_set:
                root_scores[ri] += float(row["alpha_lba_bytes"])
                root_scores[rj] += float(row["alpha_lab_bytes"])
        root_idx = min(nodes, key=lambda idx: root_scores.get(idx, 1e18))

        cluster_results.append(
            {
                "cluster_id": cid,
                "lang": lang,
                "repos": sorted(repos),
                "has_flow": "FLOW" in repos,
                "members": [str(files[idx]["label"]) for idx in nodes],
                "shared_lines": len(shared_lines),
                "sum_indep_bytes": round(indep_b, 1),
                "seq_savings_bytes": round(seq_b, 1),
                "shared_model_bytes": round(shared_b, 1),
                "delta_mdl_bytes": round(gain_b, 1),
                "hierarchy_root": str(files[root_idx]["label"]),
            }
        )

    cluster_results.sort(key=lambda c: -float(c["delta_mdl_bytes"]))
    return cluster_results


def render_markdown_report(
    files: List[Dict[str, object]],
    pair_rows: List[Dict[str, object]],
    func_rows: List[Dict[str, object]],
    clusters: List[Dict[str, object]],
    top_pairs: int,
    top_funcs: int,
) -> str:
    repos = sorted({str(f["repo"]) for f in files})
    lines: List[str] = [
        "# FLOW Ecosystem Structural MDL Audit Report (`INFO v1.0.0`)",
        "",
        f"- **Scanned Repositories ({len(repos)})**: {', '.join(repos)}",
        f"- **Indexed Source Files**: `{len(files)}` (`.c`, `.h`, `.lean`, `.py`)",
        f"- **Evaluated Cross-Repo File Pairs**: `{len(pair_rows)}` | **Evaluated Function Clones**: `{len(func_rows)}`",
        f"- **Actionable Joint-MDL Clusters (`>= 2` repos)**: `{len(clusters)}`",
        "",
        "## 1. Level 3 — Ranked `FLOW` PR Extraction Priorities (`ΔMDL > 0`)",
        "",
        "| Rank | Lang | Repos | Hierarchy Root | `L(M)` | `Sum Indep` | `Seq Savings` | `ΔMDL Gain` | Action |",
        "| ---: | --- | --- | --- | ---: | ---: | ---: | ---: | --- |",
    ]
    for idx, c in enumerate(clusters, 1):
        action = "Promote to FLOW" if not c["has_flow"] else "Align w/ FLOW"
        lines.append(
            f"| {idx} | `{c['lang']}` | {', '.join(c['repos'])} | `{c['hierarchy_root']}` | "
            f"`{c['shared_model_bytes']:.0f} B` | `{c['sum_indep_bytes']:.0f} B` | "
            f"`{c['seq_savings_bytes']:+.0f} B` | **`{c['delta_mdl_bytes']:+.0f} B`** | {action} |"
        )
    lines.append("")
    for idx, c in enumerate(clusters, 1):
        lines.append(f"### Cluster {idx}: `{' / '.join(c['repos'])}` (`{c['lang']}`, ΔMDL = `{c['delta_mdl_bytes']:+.0f} B`)")
        lines.append(f"- **Recommended Base / Hierarchy Root**: `{c['hierarchy_root']}` (`{c['shared_lines']}` shared canonical lines, `L_alpha(M) = {c['shared_model_bytes']:.0f} B`)")
        for m in c["members"]:
            lines.append(f"  - `{m}`")
        lines.append("")

    lines.extend([
        f"## 2. Level 1 vs Level 2 — Top {min(top_pairs, len(pair_rows))} Cross-Repo File Pairs (`raw_NCD` vs `alpha_NCD`)",
        "",
        "| File A | File B | `raw_NCD` | `alpha_NCD` | `I_alpha(A;B)` | `Redund%` | Hierarchy |",
        "| --- | --- | ---: | ---: | ---: | ---: | --- |",
    ])
    for r in pair_rows[:top_pairs]:
        lines.append(
            f"| `{r['a']}` | `{r['b']}` | `{r['raw_ncd']:.3f}` | **`{r['alpha_ncd']:.3f}`** | "
            f"`{r['mi_alpha_bytes']:.0f} B` | `{r['redund_alpha_pct']:.1f}%` | `{r['subsume']}` |"
        )

    lines.extend([
        "",
        f"## 3. Level 2 — Top {min(top_funcs, len(func_rows))} Isomorphic Cross-Repo Functions / Blocks",
        "",
        "| Block Span A | Block Span B | `raw_NCD` | `alpha_NCD` | `I_alpha` | `Redund%` |",
        "| --- | --- | ---: | ---: | ---: | ---: |",
    ])
    for f in func_rows[:top_funcs]:
        lines.append(
            f"| `{f['span_a']}` | `{f['span_b']}` | `{f['raw_ncd']:.3f}` | **`{f['alpha_ncd']:.3f}`** | "
            f"`{f['mi_alpha_bytes']:.0f} B` | `{f['redund_alpha_pct']:.1f}%` |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="INFO Structural MDL Ecosystem Auditor")
    parser.add_argument("--roots", nargs="+", type=Path, required=True)
    parser.add_argument("--out-md", type=Path, default=None)
    parser.add_argument("--out-json", type=Path, default=None)
    parser.add_argument("--top-pairs", type=int, default=20)
    parser.add_argument("--top-funcs", type=int, default=15)
    parser.add_argument("--max-ncd-eval", type=int, default=80)
    parser.add_argument("--max-func-eval", type=int, default=40)
    args = parser.parse_args()

    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}"
    files = discover_files(args.roots)
    repos = sorted({str(f["repo"]) for f in files})
    print(f"[INFO-Audit] Indexed {len(files)} source files across {len(repos)} repos: {', '.join(repos)}")

    with tempfile.TemporaryDirectory(prefix="info_eco_audit_") as td:
        tdir = Path(td)
        canonicalize_all(files, tdir)
        pair_rows = analyze_file_pairs(files, tdir, max_eval=args.max_ncd_eval)
        func_rows = analyze_function_clones(files, tdir, max_eval=args.max_func_eval)
        clusters = cluster_and_eval_joint_mdl(files, pair_rows, func_rows, tdir)

    print("\n  --- Top Level-3 Joint MDL FLOW PR Candidates ---")
    if clusters:
        for idx, c in enumerate(clusters[:10], 1):
            print(
                f"    #{idx} [{c['lang']:<4}] deltaMDL={c['delta_mdl_bytes']:>+7.0f}B "
                f"(seq={c['seq_savings_bytes']:>+7.0f}B, shared={c['shared_model_bytes']:.0f}B) "
                f"| repos={','.join(c['repos'])} | root={c['hierarchy_root']}"
            )
    else:
        print("    (No multi-repo clusters above threshold in scanned roots)")

    print(f"\n  --- Top Cross-Repo File Pairs (showing {min(args.top_pairs, len(pair_rows))}/{len(pair_rows)}) ---")
    for r in pair_rows[: args.top_pairs]:
        print(
            f"    {r['a']:<36} <-> {r['b']:<36} | rawNCD={r['raw_ncd']:.3f} alphaNCD={r['alpha_ncd']:.3f} "
            f"I={r['mi_alpha_bytes']:>5.0f}B ({r['redund_alpha_pct']:>4.1f}%) {r['subsume']}"
        )

    print(f"\n  --- Top Cross-Repo Function Clones (showing {min(args.top_funcs, len(func_rows))}/{len(func_rows)}) ---")
    for f in func_rows[: args.top_funcs]:
        print(
            f"    {f['span_a']:<44} <-> {f['span_b']:<44} | raw={f['raw_ncd']:.3f} alpha={f['alpha_ncd']:.3f} ({f['redund_alpha_pct']:.1f}%)"
        )

    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(
            render_markdown_report(
                files, pair_rows, func_rows, clusters, args.top_pairs, args.top_funcs
            ),
            encoding="utf-8",
        )
    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(
            json.dumps(
                {
                    "repos": repos,
                    "files_indexed": len(files),
                    "file_pairs": pair_rows,
                    "func_clones": func_rows,
                    "clusters": clusters,
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
