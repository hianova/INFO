#!/usr/bin/env python3
"""
INFO v1.0.0 — Lean 4 Kernel Proof-DAG & Proof-Term MDL Distiller
================================================================
Uses `tools/lean_expr_export.lean` (`Lean.importModules`) + Ring-0 `build/info`
(`INFO_LANG_LEAN_EXPR` α-canonicalization, `alpha-ncd`, `eval-mdl-group`, `eval-bpb`) to:
  1. Measure tree-vs-DAG expression sharing & Ring-0 kernel Proof MDL bits;
  2. Identify unreachable dead helper declarations from live target theorems;
  3. Detect α-isomorphic kernel proof-term clones & compute cluster ΔMDL gain;
  4. Rank load-bearing core backbone lemmas in the proof dependency DAG.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict, deque
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple


ROOT = Path(__file__).resolve().parent.parent
INFO_BIN = ROOT / "build" / "info"
EXPORTER = ROOT / "tools" / "lean_expr_export.lean"
Q12_BYTES = 4096.0 * 8.0


def find_lean_bin() -> Path:
    env_p = os.environ.get("LEAN")
    if env_p:
        return Path(env_p)
    w = shutil.which("lean")
    if w:
        return Path(w)
    home_p = Path.home() / ".elan" / "bin" / "lean"
    if home_p.exists():
        return home_p
    return Path("/Users/kuangtalin/.elan/bin/lean")


def run_cmd(cmd: Sequence[str], cwd: Path = ROOT, env: Optional[Dict[str, str]] = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        list(cmd),
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


def token_shingles(text: str, k: int = 5) -> Set[int]:
    toks = text.split()
    if len(toks) < k:
        return {hash(tuple(toks))} if toks else set()
    return {hash(tuple(toks[i : i + k])) for i in range(len(toks) - k + 1)}


def jaccard(a: Set[int], b: Set[int]) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    return inter / float(len(a | b)) if inter else 0.0


def eval_bpb(path: Path, out_json: Path) -> Dict[str, float]:
    res = run_cmd([str(INFO_BIN), "eval-bpb", str(path), "--out-json", str(out_json)])
    assert res.returncode == 0, f"eval-bpb failed on {path}: {res.stderr}"
    j = json.loads(out_json.read_text(encoding="utf-8"))
    orig_b = float(j["orig_bytes"])
    mdl_b = float(j["total_bits_q12"]) / Q12_BYTES
    bpb = (mdl_b * 8.0 / orig_b) if orig_b > 0 else 0.0
    return {"orig_bytes": orig_b, "mdl_bytes": round(mdl_b, 2), "bpb": round(bpb, 3)}


def export_module(module: str, prefix: str, lean_path: str, out_json: Path) -> Dict[str, object]:
    lean_bin = find_lean_bin()
    env = dict(os.environ)
    env["LEAN_PATH"] = lean_path
    res = run_cmd(
        [str(lean_bin), "--run", str(EXPORTER), module, prefix, str(out_json), lean_path],
        env=env,
    )
    assert res.returncode == 0, f"lean_expr_export failed on {module}:\n{res.stderr}\n{res.stdout}"
    return json.loads(out_json.read_text(encoding="utf-8"))


def distill_module(
    module: str,
    prefix: str,
    lean_path: str,
    targets: Optional[List[str]],
    max_pairs: int = 40,
    min_proof_dag: int = 10,
    source_files: Optional[List[Path]] = None,
    olean_bytes: Optional[int] = None,
    infp_v2_bytes: Optional[int] = None,
) -> Dict[str, object]:
    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}; run `make all` first."
    assert EXPORTER.is_file(), f"Missing {EXPORTER}"

    with tempfile.TemporaryDirectory(prefix="info_lean_distill_") as td:
        tdir = Path(td)
        exp_json = tdir / "export.json"
        raw = export_module(module, prefix, lean_path, exp_json)
        decls: List[Dict[str, object]] = list(raw["decls"])  # type: ignore[arg-type]

        by_name: Dict[str, Dict[str, object]] = {str(d["name"]): d for d in decls}
        user_decls = [d for d in decls if "._proof_" not in str(d["name"])]

        # 1. Reachability & Dead Declaration Detection (preserve ._proof_ edges in BFS)
        if targets:
            seeds = [t for t in targets if t in by_name]
        else:
            seeds = [
                str(d["name"])
                for d in user_decls
                if str(d["kind"]) == "thm" and "_private." not in str(d["name"])
            ]
        live_set: Set[str] = set(seeds)
        q: deque[str] = deque(seeds)
        while q:
            cur = q.popleft()
            d = by_name.get(cur)
            if d is None:
                continue
            for dep in d["deps"]:  # type: ignore[attr-defined]
                ds = str(dep)
                if ds in by_name and ds not in live_set:
                    live_set.add(ds)
                    q.append(ds)

        dead_decls = [
            {
                "name": d["name"],
                "kind": d["kind"],
                "proof_dag_nodes": d["proof_dag_nodes"],
                "proof_tree_nodes": d["proof_tree_nodes"],
                "expr_bytes": len(str(d["expr_tokens"]).encode("utf-8")),
            }
            for d in user_decls
            if str(d["name"]) not in live_set
        ]
        dead_decls.sort(key=lambda x: (-int(x["proof_dag_nodes"]), str(x["name"])))
        live_user_count = sum(1 for d in user_decls if str(d["name"]) in live_set)

        # 2. Proof Tree vs DAG & Ring-0 Compressed Proof MDL Telemetry
        total_tree = sum(int(d["proof_tree_nodes"]) for d in decls)
        total_dag = sum(int(d["proof_dag_nodes"]) for d in decls)
        dag_ratio = (total_tree / float(max(1, total_dag)))

        all_expr_p = tdir / "all_expr.txt"
        all_expr_text = "\n".join(str(d["expr_tokens"]) for d in decls) + ("\n" if decls else "")
        all_expr_p.write_text(all_expr_text, encoding="utf-8")
        raw_mdl = eval_bpb(all_expr_p, tdir / "raw_bpb.json")

        all_canon_p = tdir / "all_expr.canon"
        rc_ac = run_cmd([str(INFO_BIN), "alpha-canon", str(all_expr_p), str(all_canon_p), "--lang", "expr"])
        assert rc_ac.returncode == 0, rc_ac.stderr
        alpha_mdl = eval_bpb(all_canon_p, tdir / "alpha_bpb.json")

        # 3. Reverse Reachability Blueprint (Load-Bearing Core Theorems)
        rev_adj: Dict[str, List[str]] = defaultdict(list)
        in_deg: Dict[str, int] = defaultdict(int)
        for d in decls:
            nm = str(d["name"])
            for dep in d["deps"]:  # type: ignore[attr-defined]
                ds = str(dep)
                if ds in by_name and ds != nm:
                    rev_adj[ds].append(nm)
                    in_deg[ds] += 1

        blueprint: List[Dict[str, object]] = []
        for d in user_decls:
            nm = str(d["name"])
            seen_up: Set[str] = set()
            dq: deque[str] = deque(rev_adj.get(nm, []))
            while dq:
                u = dq.popleft()
                if u not in seen_up:
                    seen_up.add(u)
                    dq.extend(rev_adj.get(u, []))
            blueprint.append(
                {
                    "name": nm,
                    "kind": d["kind"],
                    "in_degree": in_deg.get(nm, 0),
                    "reverse_reach": len(seen_up),
                    "proof_dag_nodes": int(d["proof_dag_nodes"]),
                    "proof_tree_nodes": int(d["proof_tree_nodes"]),
                    "reachable": nm in live_set,
                }
            )
        blueprint.sort(
            key=lambda x: (-int(x["reverse_reach"]), -int(x["in_degree"]), -int(x["proof_dag_nodes"]))
        )

        # 4. Pairwise Alpha-Isomorphic Proof-Term Clones & Joint ΔMDL Clusters
        cands_decl: List[Dict[str, object]] = []
        for idx, d in enumerate(user_decls):
            toks = str(d["expr_tokens"])
            if int(d["proof_dag_nodes"]) >= min_proof_dag and len(toks.split()) >= 12:
                src_p = tdir / f"d_{idx}.expr"
                can_p = tdir / f"d_{idx}.canon"
                src_p.write_text(toks + "\n", encoding="utf-8")
                cands_decl.append(
                    {
                        "cid": len(cands_decl),
                        "name": d["name"],
                        "kind": d["kind"],
                        "proof_dag_nodes": int(d["proof_dag_nodes"]),
                        "src_path": src_p,
                        "canon_path": can_p,
                    }
                )

        def _canon_one(item: Dict[str, object]) -> None:
            r = run_cmd([
                str(INFO_BIN), "alpha-canon",
                str(item["src_path"]), str(item["canon_path"]), "--lang", "expr",
            ])
            assert r.returncode == 0, r.stderr
            ctext = Path(item["canon_path"]).read_text(encoding="utf-8")  # type: ignore[arg-type]
            item["canon_text"] = ctext
            item["shingles"] = token_shingles(ctext, k=5)

        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
            list(ex.map(_canon_one, cands_decl))

        pair_cands: List[Tuple[float, int, int]] = []
        nc = len(cands_decl)
        for i in range(nc):
            si = cands_decl[i]["shingles"]  # type: ignore[assignment]
            for j in range(i + 1, nc):
                jac = jaccard(si, cands_decl[j]["shingles"])  # type: ignore[arg-type]
                if jac >= 0.28:
                    pair_cands.append((jac, i, j))
        pair_cands.sort(key=lambda x: (-x[0], x[1], x[2]))
        pair_cands = pair_cands[:max_pairs]

        def _eval_pair(item: Tuple[int, Tuple[float, int, int]]) -> Dict[str, object]:
            k, (jac, i, j) = item
            di, dj = cands_decl[i], cands_decl[j]
            out_j = tdir / f"ncd_{k}.json"
            r = run_cmd([
                str(INFO_BIN), "alpha-ncd",
                str(di["src_path"]), str(dj["src_path"]), "--lang", "expr", "--out-json", str(out_j),
            ])
            assert r.returncode == 0, r.stderr
            jv = json.loads(out_j.read_text(encoding="utf-8"))
            rla = max(1e-9, jv["raw_la_q12"] / Q12_BYTES)
            rlb = max(1e-9, jv["raw_lb_q12"] / Q12_BYTES)
            rlba = jv["raw_lba_q12"] / Q12_BYTES
            rlab = jv["raw_lab_q12"] / Q12_BYTES
            ala = max(1e-9, jv["alpha_la_q12"] / Q12_BYTES)
            alb = max(1e-9, jv["alpha_lb_q12"] / Q12_BYTES)
            alba = jv["alpha_lba_q12"] / Q12_BYTES
            alab = jv["alpha_lab_q12"] / Q12_BYTES
            raw_ncd = max(0.0, (min(rla + rlba, rlb + rlab) - min(rla, rlb)) / max(rla, rlb))
            alpha_ncd = max(0.0, (min(ala + alba, alb + alab) - min(ala, alb)) / max(ala, alb))
            redund_pct = max(max(0.0, alb - alba) / alb, max(0.0, ala - alab) / ala) * 100.0
            return {
                "i": i,
                "j": j,
                "name_a": di["name"],
                "name_b": dj["name"],
                "jaccard": round(jac, 3),
                "raw_ncd": round(raw_ncd, 3),
                "alpha_ncd": round(alpha_ncd, 3),
                "redund_alpha_pct": round(redund_pct, 1),
            }

        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as ex:
            clone_pairs = list(ex.map(_eval_pair, enumerate(pair_cands)))
        clone_pairs.sort(key=lambda r: (float(r["alpha_ncd"]), -float(r["redund_alpha_pct"])))

        # Cluster α-isomorphic proof clones & compute exact Joint ΔMDL
        parent = list(range(nc))

        def find(x: int) -> int:
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        active: Set[int] = set()
        for pr in clone_pairs:
            if float(pr["alpha_ncd"]) < 0.25 or float(pr["redund_alpha_pct"]) >= 80.0:
                ra, rb = find(int(pr["i"])), find(int(pr["j"]))
                if ra != rb:
                    parent[rb] = ra
                active.add(int(pr["i"]))
                active.add(int(pr["j"]))

        groups: Dict[int, List[int]] = defaultdict(list)
        for idx in sorted(active):
            groups[find(idx)].append(idx)

        clone_clusters: List[Dict[str, object]] = []
        for gidx, members in enumerate(groups.values()):
            if len(members) < 2:
                continue
            members = members[:16]
            rep = min(members, key=lambda idx: len(str(cands_decl[idx]["canon_text"])))
            out_g = tdir / f"grp_{gidx}.json"
            r = run_cmd([
                str(INFO_BIN), "eval-mdl-group", "--alpha", "--lang", "expr",
                "--shared", str(cands_decl[rep]["src_path"]), "--out-json", str(out_g),
                *[str(cands_decl[idx]["src_path"]) for idx in members],
            ])
            assert r.returncode == 0, r.stderr
            jm = json.loads(out_g.read_text(encoding="utf-8"))
            clone_clusters.append(
                {
                    "rep": cands_decl[rep]["name"],
                    "members": [cands_decl[idx]["name"] for idx in members],
                    "shared_model_bytes": round(jm["shared_bits_q12"] / Q12_BYTES, 1),
                    "sum_indep_bytes": round(jm["sum_indep_bits_q12"] / Q12_BYTES, 1),
                    "seq_savings_bytes": round(jm["joint_savings_bits_q12"] / Q12_BYTES, 1),
                    "delta_mdl_bytes": round(jm["extract_gain_bits_q12"] / Q12_BYTES, 1),
                }
            )
        clone_clusters.sort(key=lambda c: -float(c["delta_mdl_bytes"]))

        axioms_used = sorted({ax for d in decls for ax in d["axioms"]})  # type: ignore[attr-defined]

        # 5. Interface Over-Specification Audit: Dead Structure Fields & Unused Theorem Hypotheses
        live_proj_uses: Set[str] = {
            str(p)
            for d in decls
            if str(d["name"]) in live_set
            for p in d.get("proj_uses", [])  # type: ignore[attr-defined]
        }
        live_deps: Set[str] = {
            str(dep)
            for d in decls
            if str(d["name"]) in live_set
            for dep in d.get("deps", [])  # type: ignore[attr-defined]
        }
        structures = list(raw.get("structures", []))  # type: ignore[arg-type]
        dead_fields: List[Dict[str, object]] = []
        for st in structures:
            sname = str(st["name"])
            fields = [str(f) for f in st.get("fields", [])]  # type: ignore[union-attr]
            is_live_struct = (
                any(dep == sname or dep.startswith(sname + ".") for dep in live_deps)
                or any(p.startswith(sname + "#") for p in live_proj_uses)
            )
            if not is_live_struct:
                continue
            for fidx, fname in enumerate(fields):
                if f"{sname}#{fidx}" not in live_proj_uses and f"{sname}.{fname}" not in live_deps:
                    dead_fields.append({"structure": sname, "field": fname, "index": fidx})

        unused_hyps: List[Dict[str, object]] = []
        for d in user_decls:
            nm = str(d["name"])
            hyps = list(d.get("unused_hyps", []))  # type: ignore[arg-type]
            if nm in live_set and hyps:
                unused_hyps.append({"name": nm, "hyps": hyps})

        # 6. Dual-Layer Proof MDL (L_source vs L_kernel & .olean Bloat Telemetry)
        dual_layer_mdl: Dict[str, object] = {
            "total_dag_nodes": total_dag,
            "total_tree_nodes": total_tree,
            "kernel_expr_mdl_bytes": alpha_mdl["mdl_bytes"],
        }
        if source_files:
            existing_srcs = [p for p in source_files if p.is_file()]
            if existing_srcs:
                src_concat = tdir / "source_concat.lean"
                src_concat.write_bytes(b"\n".join(p.read_bytes() for p in existing_srcs))
                src_m = eval_bpb(src_concat, tdir / "src_bpb.json")
                dual_layer_mdl["source_orig_bytes"] = src_m["orig_bytes"]
                dual_layer_mdl["source_mdl_bytes"] = src_m["mdl_bytes"]
                dual_layer_mdl["source_bpb"] = src_m["bpb"]
                dual_layer_mdl["tactic_leverage_dag_per_src_b"] = round(
                    total_dag / max(1.0, float(src_m["mdl_bytes"])), 3
                )
        if infp_v2_bytes is not None:
            dual_layer_mdl["infp_v2_bytes"] = int(infp_v2_bytes)
            if "source_mdl_bytes" in dual_layer_mdl:
                dual_layer_mdl["kernel_to_source_ratio"] = round(
                    float(infp_v2_bytes) / max(1.0, float(dual_layer_mdl["source_mdl_bytes"])), 3
                )
        if olean_bytes is not None:
            dual_layer_mdl["olean_bytes"] = int(olean_bytes)
            if infp_v2_bytes is not None and infp_v2_bytes > 0:
                dual_layer_mdl["olean_to_infp_ratio"] = round(float(olean_bytes) / float(infp_v2_bytes), 2)

        return {
            "module": module,
            "prefix": prefix,
            "decl_count": len(user_decls),
            "live_count": live_user_count,
            "dead_count": len(dead_decls),
            "structures_count": len(structures),
            "total_tree_nodes": total_tree,
            "total_dag_nodes": total_dag,
            "dag_share_ratio": round(dag_ratio, 2),
            "raw_expr_mdl": raw_mdl,
            "alpha_expr_mdl": alpha_mdl,
            "dual_layer_mdl": dual_layer_mdl,
            "axioms_used": axioms_used,
            "dead_decls": dead_decls,
            "dead_fields": dead_fields,
            "unused_hyps": unused_hyps,
            "clone_pairs": clone_pairs,
            "clone_clusters": clone_clusters,
            "blueprint_top": blueprint[:15],
        }


def render_markdown(rep: Dict[str, object]) -> str:
    raw_m = rep["raw_expr_mdl"]  # type: ignore[index]
    alp_m = rep["alpha_expr_mdl"]  # type: ignore[index]
    lines = [
        f"# Lean 4 Proof-DAG & MDL Distillation Report: `{rep['module']}`",
        "",
        f"- **Declarations**: `{rep['decl_count']}` (live=`{rep['live_count']}`, dead=`{rep['dead_count']}`)",
        f"- **Proof Tree vs DAG Nodes**: `{rep['total_tree_nodes']}` tree -> `{rep['total_dag_nodes']}` DAG (`{rep['dag_share_ratio']}x` structural sharing)",
        f"- **Ring-0 Proof MDL (`raw` -> `alpha`)**: `{raw_m['orig_bytes']:.0f} B` ({raw_m['mdl_bytes']:.1f} B @ `{raw_m['bpb']} bpb`) -> `{alp_m['orig_bytes']:.0f} B` ({alp_m['mdl_bytes']:.1f} B @ `{alp_m['bpb']} bpb`)",
        f"- **Axioms Detected**: `{', '.join(rep['axioms_used']) or '(none)'}`",  # type: ignore[arg-type]
        "",
        "## 1. α-Isomorphic Proof-Term Factoring Clusters",
        "",
        "| Representative | Members | `L(M)` | `Sum Indep` | `ΔMDL Gain` |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for c in rep["clone_clusters"]:  # type: ignore[attr-defined]
        lines.append(
            f"| `{c['rep']}` | {len(c['members'])} | `{c['shared_model_bytes']:.1f} B` | `{c['sum_indep_bytes']:.1f} B` | **`{c['delta_mdl_bytes']:+.1f} B`** |"
        )
    if not rep["clone_clusters"]:
        lines.append("| *(No α-isomorphic proof clone clusters above threshold)* | 0 | - | - | - |")

    lines.extend(["", "## 2. Unreachable Dead Declarations", ""])
    if rep["dead_decls"]:
        lines.extend(["| Declaration | Kind | DAG Nodes | Tree Nodes |", "| --- | --- | ---: | ---: |"])
        for d in rep["dead_decls"][:20]:  # type: ignore[index]
            lines.append(
                f"| `{d['name']}` | `{d['kind']}` | `{d['proof_dag_nodes']}` | `{d['proof_tree_nodes']}` |"
            )
    else:
        lines.append("*(No unreachable declarations)*")

    lines.extend([
        "",
        "## 3. Load-Bearing Core Theorem Blueprint (Top 15)",
        "",
        "| Rank | Declaration | Reverse Reach | In-Deg | DAG Nodes |",
        "| ---: | --- | ---: | ---: | ---: |",
    ])
    for idx, b in enumerate(rep["blueprint_top"], 1):  # type: ignore[arg-type]
        lines.append(
            f"| {idx} | `{b['name']}` | `{b['reverse_reach']}` | `{b['in_degree']}` | `{b['proof_dag_nodes']}` |"
        )
    dual = rep.get("dual_layer_mdl", {})  # type: ignore[assignment]
    if isinstance(dual, dict) and "source_mdl_bytes" in dual:
        lines.extend([
            "",
            "## 4. Dual-Layer Proof MDL & Interface Audit",
            "",
            f"- **Source MDL (`L_source`)**: `{dual['source_orig_bytes']:.0f} B` -> `{dual['source_mdl_bytes']:.1f} B` (`{dual['source_bpb']} bpb`)",
            f"- **Tactic Leverage (`DAG / L_source`)**: `{dual['tactic_leverage_dag_per_src_b']} nodes/B`",
            f"- **Dead Structure Fields**: `{len(rep.get('dead_fields', []))}` | **Unused Theorem Hypotheses**: `{len(rep.get('unused_hyps', []))}`",
        ])
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="INFO Lean 4 Proof-DAG & MDL Distiller")
    parser.add_argument("--module", required=True)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--lean-path", default="build/lean")
    parser.add_argument("--targets", default=None, help="Comma-separated target declarations")
    parser.add_argument("--max-pairs", type=int, default=40)
    parser.add_argument("--min-proof-dag", type=int, default=10)
    parser.add_argument("--source-files", default=None, help="Comma-separated .lean source files for L_source")
    parser.add_argument("--olean-bytes", type=int, default=None)
    parser.add_argument("--out-json", type=Path, default=None)
    parser.add_argument("--out-md", type=Path, default=None)
    args = parser.parse_args()

    tlist = [t.strip() for t in args.targets.split(",") if t.strip()] if args.targets else None
    sfiles = [Path(s.strip()) for s in args.source_files.split(",") if s.strip()] if args.source_files else None
    rep = distill_module(
        args.module,
        args.prefix,
        args.lean_path,
        tlist,
        max_pairs=args.max_pairs,
        min_proof_dag=args.min_proof_dag,
        source_files=sfiles,
        olean_bytes=args.olean_bytes,
    )
    raw_m = rep["raw_expr_mdl"]  # type: ignore[index]
    alp_m = rep["alpha_expr_mdl"]  # type: ignore[index]
    print(
        f"[Lean-Distill] {rep['module']}: decls={rep['decl_count']} (live={rep['live_count']}, dead={rep['dead_count']}) | "
        f"tree={rep['total_tree_nodes']} -> dag={rep['total_dag_nodes']} ({rep['dag_share_ratio']}x) | "
        f"MDL raw={raw_m['mdl_bytes']}B -> alpha={alp_m['mdl_bytes']}B | clones={len(rep['clone_clusters'])}"
    )
    if args.out_json is not None:
        args.out_json.parent.mkdir(parents=True, exist_ok=True)
        args.out_json.write_text(json.dumps(rep, indent=2) + "\n", encoding="utf-8")
    if args.out_md is not None:
        args.out_md.parent.mkdir(parents=True, exist_ok=True)
        args.out_md.write_text(render_markdown(rep), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
