#!/usr/bin/env python3
"""
INFO v1.0.0 — Experiment 6: Lean 4 Kernel Proof-DAG & Proof-Term MDL Distillation
================================================================================
Part 1 (Soundness-Preserving Compression Ground Truth):
  Compiles a synthetic Lean 4 library `BloatedDemo.lean` containing 2 unreachable
  dead theorems + 4 α-isomorphic proof clones feeding `headline_main`, verifies
  `tools/info_lean_distill.py` isolates both dead declarations and the 4-clone
  joint-ΔMDL group, then compiles the distilled `DistilledDemo.lean` under
  `-DwarningAsError=true` + `leanchecker` and proves type equivalence + strict
  reduction in kernel DAG nodes & compressed Proof MDL bytes.
Part 2 (Live Ecosystem Proof-DAG Audit):
  Audits `Info.Theory` (plus compiled sibling Lean libraries when present) and
  reports Proof Tree vs DAG sharing, Ring-0 `INFO_LANG_LEAN_EXPR` MDL, and
  load-bearing core backbone lemmas.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Tuple


ROOT = Path(__file__).resolve().parent.parent
INFO_BIN = ROOT / "build" / "info"
TOOLS_DIR = ROOT / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

from info_lean_distill import distill_module, find_lean_bin  # type: ignore  # noqa: E402


BLOATED_LEAN = """/- Synthetic bloated Lean proof module for soundness-preserving MDL test -/

namespace BloatedDemo

structure DemoCfg where
  scale : Nat
  unused_meta : Nat

theorem helper_over_spec (cfg : DemoCfg) (_h_unused : 0 = 0) :
    cfg.scale + 0 = cfg.scale := by
  omega

theorem dead_thm_1 (a b : Nat) : a + b + (a + b) = 2 * (a + b) := by
  omega

theorem dead_thm_2 (xs : List Nat) (n : Nat) :
    (xs ++ [n]).length = xs.length + 1 := by
  simp

theorem iso_a (fA : Nat → Nat) (xs : List Nat) :
    ((xs.map fA).reverse).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.map_cons, List.reverse_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem iso_b (fB : Nat → Nat) (ys : List Nat) :
    ((ys.map fB).reverse).length = ys.length := by
  induction ys with
  | nil => rfl
  | cons y tl ih =>
    simp only [List.map_cons, List.reverse_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem iso_c (fC : Nat → Nat) (zs : List Nat) :
    ((zs.map fC).reverse).length = zs.length := by
  induction zs with
  | nil => rfl
  | cons z tl ih =>
    simp only [List.map_cons, List.reverse_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem iso_d (fD : Nat → Nat) (ws : List Nat) :
    ((ws.map fD).reverse).length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w tl ih =>
    simp only [List.map_cons, List.reverse_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem headline_main (g1 g2 : Nat → Nat) (s1 s2 s3 s4 : List Nat) :
    ((s1.map g1).reverse).length + ((s2.map g2).reverse).length +
      ((s3.map g1).reverse).length + ((s4.map g2).reverse).length =
        s1.length + s2.length + s3.length + s4.length := by
  have h1 := iso_a g1 s1
  have h2 := iso_b g2 s2
  have h3 := iso_c g1 s3
  have h4 := iso_d g2 s4
  have hcfg := helper_over_spec { scale := s1.length, unused_meta := 99 } rfl
  omega

end BloatedDemo
"""

DISTILLED_LEAN = """/- Soundness-preserving distilled module: 0 dead lemmas, minimal interface, shared core -/

namespace DistilledDemo

structure DemoCfg where
  scale : Nat

theorem helper_minimal (cfg : DemoCfg) :
    cfg.scale + 0 = cfg.scale := by
  omega

theorem shared_rev_map_len (f : Nat → Nat) (xs : List Nat) :
    ((xs.map f).reverse).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.map_cons, List.reverse_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem headline_main (g1 g2 : Nat → Nat) (s1 s2 s3 s4 : List Nat) :
    ((s1.map g1).reverse).length + ((s2.map g2).reverse).length +
      ((s3.map g1).reverse).length + ((s4.map g2).reverse).length =
        s1.length + s2.length + s3.length + s4.length := by
  have h1 := shared_rev_map_len g1 s1
  have h2 := shared_rev_map_len g2 s2
  have h3 := shared_rev_map_len g1 s3
  have h4 := shared_rev_map_len g2 s4
  have hcfg := helper_minimal { scale := s1.length }
  omega

end DistilledDemo
"""


def _compile_and_check(lean_bin: Path, src_path: Path, olean_path: Path, mod: str, search_dir: Path) -> str:
    env = dict(os.environ)
    env["LEAN_PATH"] = str(search_dir)
    c = subprocess.run(
        [str(lean_bin), "-DwarningAsError=true", f"--root={search_dir}", "-o", str(olean_path), str(src_path)],
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    assert c.returncode == 0, f"Compile failed for {mod}:\n{c.stderr}\n{c.stdout}"

    lc_bin = lean_bin.parent / "leanchecker"
    chk = subprocess.run([str(lc_bin), mod], env=env, capture_output=True, text=True, check=False)
    assert chk.returncode == 0, f"leanchecker failed for {mod}:\n{chk.stderr}\n{chk.stdout}"

    ax = subprocess.run(
        [str(lean_bin), "--stdin"],
        input=f"import {mod}\n#print axioms {mod}.headline_main\n#check @{mod}.headline_main\n",
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    assert ax.returncode == 0, f"axiom/type check failed for {mod}:\n{ax.stdout}\n{ax.stderr}"
    assert "sorryAx" not in ax.stdout and "Lean.ofReduceBool" not in ax.stdout
    return ax.stdout


def run_part1_soundness_preserving_compression() -> None:
    print("  --- Part 1: Soundness-Preserving Lean Proof-DAG Compression ---")
    lean_bin = find_lean_bin()
    with tempfile.TemporaryDirectory(prefix="info_proof_mdl_") as td:
        tdir = Path(td)
        p_bloat = tdir / "BloatedDemo.lean"
        o_bloat = tdir / "BloatedDemo.olean"
        p_dist = tdir / "DistilledDemo.lean"
        o_dist = tdir / "DistilledDemo.olean"
        p_bloat.write_text(BLOATED_LEAN, encoding="utf-8")
        p_dist.write_text(DISTILLED_LEAN, encoding="utf-8")

        out_bloat = _compile_and_check(lean_bin, p_bloat, o_bloat, "BloatedDemo", tdir)
        out_dist = _compile_and_check(lean_bin, p_dist, o_dist, "DistilledDemo", tdir)

        rep_b = distill_module(
            "BloatedDemo",
            "BloatedDemo",
            str(tdir),
            targets=["BloatedDemo.headline_main"],
            source_files=[p_bloat],
            olean_bytes=o_bloat.stat().st_size,
        )
        rep_d = distill_module(
            "DistilledDemo",
            "DistilledDemo",
            str(tdir),
            targets=["DistilledDemo.headline_main"],
            source_files=[p_dist],
            olean_bytes=o_dist.stat().st_size,
        )

        dead_names = {d["name"] for d in rep_b["dead_decls"]}  # type: ignore[attr-defined]
        assert dead_names == {
            "BloatedDemo.dead_thm_1",
            "BloatedDemo.dead_thm_2",
            "BloatedDemo.DemoCfg.unused_meta",
        }, dead_names
        assert rep_d["dead_count"] == 0, rep_d["dead_decls"]

        dead_fields_b = {(df["structure"], df["field"]) for df in rep_b["dead_fields"]}  # type: ignore[attr-defined]
        assert ("BloatedDemo.DemoCfg", "unused_meta") in dead_fields_b, rep_b["dead_fields"]
        assert len(rep_d["dead_fields"]) == 0, rep_d["dead_fields"]  # type: ignore[arg-type]

        unused_b = {u["name"]: u["hyps"] for u in rep_b["unused_hyps"]}  # type: ignore[attr-defined]
        assert "_h_unused" in unused_b.get("BloatedDemo.helper_over_spec", []), rep_b["unused_hyps"]
        assert len(rep_d["unused_hyps"]) == 0, rep_d["unused_hyps"]  # type: ignore[arg-type]

        clusters = rep_b["clone_clusters"]  # type: ignore[assignment]
        assert len(clusters) >= 1 and len(clusters[0]["members"]) == 4, clusters
        assert float(clusters[0]["delta_mdl_bytes"]) > 0.0, clusters

        # Ensure type signatures remain identical (modulo module prefix) and strict compression achieved
        sig_b = out_bloat.splitlines()[-1].replace("BloatedDemo.", "")
        sig_d = out_dist.splitlines()[-1].replace("DistilledDemo.", "")
        assert sig_b == sig_d, f"Signature mismatch: {sig_b!r} vs {sig_d!r}"

        dag_b = int(rep_b["total_dag_nodes"])  # type: ignore[arg-type]
        dag_d = int(rep_d["total_dag_nodes"])  # type: ignore[arg-type]
        mdl_b = float(rep_b["alpha_expr_mdl"]["mdl_bytes"])  # type: ignore[index]
        mdl_d = float(rep_d["alpha_expr_mdl"]["mdl_bytes"])  # type: ignore[index]
        src_mdl_b = float(rep_b["dual_layer_mdl"]["source_mdl_bytes"])  # type: ignore[index]
        src_mdl_d = float(rep_d["dual_layer_mdl"]["source_mdl_bytes"])  # type: ignore[index]
        assert dag_d < dag_b and mdl_d < mdl_b and src_mdl_d < src_mdl_b

        print(
            f"    BloatedDemo  : decls={rep_b['decl_count']} (dead=2, dead_fields={len(rep_b['dead_fields'])}, "  # type: ignore[arg-type]
            f"unused_hyps={len(rep_b['unused_hyps'])}), clones=4 (ΔMDL={clusters[0]['delta_mdl_bytes']:+.1f} B), "  # type: ignore[arg-type]
            f"L_src={src_mdl_b:.1f} B, DAG={dag_b}, α-MDL={mdl_b:.1f} B"
        )
        print(
            f"    DistilledDemo: decls={rep_d['decl_count']} (dead=0, dead_fields=0, unused_hyps=0), leanchecker PASS, "
            f"L_src={src_mdl_d:.1f} B (-{src_mdl_b - src_mdl_d:.1f} B), DAG={dag_d} (-{dag_b - dag_d}), α-MDL={mdl_d:.1f} B (-{mdl_b - mdl_d:.1f} B)"
        )


def run_part2_ecosystem_lean_audit() -> None:
    print("  --- Part 2: Live Ecosystem Lean Kernel Proof-DAG Audit ---")
    candidates: List[Tuple[str, str, str, Path, List[Path]]] = [
        ("Info.Theory", "Info", str(ROOT / "build" / "lean"), ROOT / "build" / "lean" / "Info" / "Theory.olean", sorted((ROOT / "Info").glob("*.lean"))),
        ("Flow.Math", "Flow", str(ROOT.parent / "FLOW" / "build" / "lean"), ROOT.parent / "FLOW" / "build" / "lean" / "Flow" / "Math.olean", sorted((ROOT.parent / "FLOW" / "core" / "lean" / "Flow").glob("*.lean")) + sorted((ROOT.parent / "FLOW" / "sdk" / "lean" / "Flow").glob("*.lean"))),
        ("Sound.Theory", "Sound", str(ROOT.parent / "SOUND" / "build" / "lean"), ROOT.parent / "SOUND" / "build" / "lean" / "Sound" / "Theory.olean", []),
        ("Phy.Noether", "Phy", f"{ROOT.parent / 'PHY' / 'build' / 'lean'}:{ROOT.parent / 'FLOW' / 'build' / 'lean'}", ROOT.parent / "PHY" / "build" / "lean" / "Phy" / "Noether.olean", []),
        ("EleCert", "EleCert", f"{ROOT.parent / 'FLOW' / 'build' / 'lean'}:{ROOT.parent / 'ELE' / 'build'}", ROOT.parent / "ELE" / "build" / "EleCert.olean", []),
        ("EconCert", "EconCert", f"{ROOT.parent / 'FLOW' / 'build' / 'lean'}:{ROOT.parent / 'ECON' / 'build'}", ROOT.parent / "ECON" / "build" / "EconCert.olean", []),
        ("ChemCert", "ChemCert", str(ROOT.parent / "FLOW" / "build" / "lean") + ":" + str(ROOT.parent / "CHEM" / "build"), ROOT.parent / "CHEM" / "build" / "ChemCert.olean", []),
    ]
    audited = 0
    for mod, pfx, lpath, olean, src_files in candidates:
        if not olean.is_file():
            continue
        rep = distill_module(mod, pfx, lpath, targets=None, max_pairs=32, min_proof_dag=14, source_files=src_files or None)
        axioms = set(rep["axioms_used"])  # type: ignore[arg-type]
        assert "sorryAx" not in axioms and "Lean.ofReduceBool" not in axioms, f"Illegal axiom in {mod}: {axioms}"
        raw_m = rep["raw_expr_mdl"]  # type: ignore[index]
        alp_m = rep["alpha_expr_mdl"]  # type: ignore[index]
        top_bp = rep["blueprint_top"][0]["name"] if rep["blueprint_top"] else "-"  # type: ignore[index]
        dual = rep.get("dual_layer_mdl", {})  # type: ignore[assignment]
        src_tag = f" src={dual['source_mdl_bytes']:.0f}B" if isinstance(dual, dict) and "source_mdl_bytes" in dual else ""
        print(
            f"    {mod:<13} | decls={rep['decl_count']:<3} dead={rep['dead_count']:<2} "
            f"df={len(rep.get('dead_fields', [])):<2} uh={len(rep.get('unused_hyps', [])):<2} | "  # type: ignore[arg-type]
            f"tree={rep['total_tree_nodes']:<8} dag={rep['total_dag_nodes']:<6} ({rep['dag_share_ratio']}x) | "
            f"MDL {raw_m['mdl_bytes']:>6.1f}B -> α:{alp_m['mdl_bytes']:>6.1f}B{src_tag} | "
            f"clones={len(rep['clone_clusters'])} | core={top_bp}"
        )
        audited += 1
    assert audited >= 1


def main() -> int:
    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}"
    print("[Experiment 6] INFO v1.0.0 Lean 4 Kernel Proof-DAG & Proof-Term MDL Distillation")
    run_part1_soundness_preserving_compression()
    run_part2_ecosystem_lean_audit()
    print("  [PASS] Soundness-preserving Proof-DAG pruning, α-clone factoring, and kernel audit verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
