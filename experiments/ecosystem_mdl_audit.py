#!/usr/bin/env python3
"""
INFO v1.0.0 — Experiment 5: Structural α-Canonicalization & Ecosystem MDL Audit
=================================================================================
Part 1 (CI-portable Ground Truth):
  Verifies that α-canonicalization eliminates domain-prefix obfuscation across
  C17, Lean4, and Python clones (`NCD_alpha << NCD_raw`), yields strictly positive
  ΔMDL when extracting a real shared abstraction, and strictly negative ΔMDL
  ("no free abstraction") when forcing an unrelated shared block.
Part 2 (Live Ecosystem Audit):
  Invokes `tools/info_ecosystem_audit.py` across FLOW, INFO, and any available
  sibling repositories (ELE, CHEM, QUA, ECON, PHY, SOUND) to rank real
  cross-repo structural duplication candidates for promotion into FLOW.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
INFO_BIN = ROOT / "build" / "info"
AUDIT_TOOL = ROOT / "tools" / "info_ecosystem_audit.py"


def run_part1_synthetic_ground_truth() -> None:
    print("  --- Part 1: CI-Portable α-Clone & Joint ΔMDL Ground-Truth ---")
    # Rich multi-function C17 clones (different prefixes/comments/constants/local vars)
    c_ele = (
        "/* ELE Ring-0 circuit hash verifier */\n"
        "static uint64_t ele_mix_hash(const uint32_t *ele_arr, uint32_t ele_n, uint64_t ele_seed) {\n"
        "    uint64_t ele_h = ele_seed ^ UINT64_C(0xCBF29CE484222325);\n"
        "    for (uint32_t ele_i = 0; ele_i < ele_n; ele_i++) {\n"
        "        uint64_t ele_w = flow_ir_eval_u64(ele_arr, ele_i & 63U);\n"
        "        ele_h ^= (ele_w << 16U) | (ele_w >> 8U);\n"
        "        ele_h *= UINT64_C(0x100000001B3);\n"
        "    }\n"
        "    return ele_h;\n"
        "}\n"
    )
    c_econ = (
        "/* ECON settlement book\n * FNV-like mixing loop */\n"
        "static uint64_t econ_settle_digest(const uint32_t *econ_slots, uint32_t econ_len, uint64_t econ_iv) {\n"
        "    uint64_t econ_acc = econ_iv ^ UINT64_C(0x9E3779B97F4A7C15);\n"
        "    for (uint32_t econ_k = 0; econ_k < econ_len; econ_k++) {\n"
        "        uint64_t econ_item = flow_ir_eval_u64(econ_slots, econ_k & 63U);\n"
        "        econ_acc ^= (econ_item << 16U) | (econ_item >> 8U);\n"
        "        econ_acc *= UINT64_C(0x27D4EB2F165667C5);\n"
        "    }\n"
        "    return econ_acc;\n"
        "}\n"
    )
    c_unrel = (
        "typedef struct { int32_t x_pos; int32_t y_pos; uint8_t color_id; } PixelTile;\n"
        "void paint_canvas(PixelTile *tiles, size_t n_tiles, int32_t dx, int32_t dy) {\n"
        "    if (tiles == NULL || n_tiles == 0U) return;\n"
        "    for (size_t row = 0U; row < n_tiles; row += 2U) {\n"
        "        tiles[row].x_pos = (tiles[row].x_pos + dx) & 255;\n"
        "        tiles[row].y_pos = (tiles[row].y_pos - dy) & 255;\n"
        "        tiles[row].color_id = (uint8_t)((tiles[row].x_pos ^ tiles[row].y_pos) & 15);\n"
        "    }\n"
        "}\n"
    )
    lean_1 = (
        "-- ELE safety invariant\n"
        "theorem ele_bound_safe (ele_a ele_b : Nat) (h1 : ele_a + 16 ≤ ele_b) : ele_a < ele_b + 1 := by omega\n"
    )
    lean_2 = (
        "-- PHY energy bound invariant\n"
        "theorem phy_action_pos (phy_p phy_q : Nat) (hx : phy_p + 16 ≤ phy_q) : phy_p < phy_q + 1 := by omega\n"
    )
    py_1 = (
        "# CHEM dual screener\n"
        "def chem_check_dual(chem_vec: list[int], chem_lim: int) -> bool:\n"
        "    chem_acc = 0\n"
        "    for chem_item in chem_vec:\n"
        "        chem_acc += chem_item * 31\n"
        "    return chem_acc <= chem_lim\n"
    )
    py_2 = (
        "# ELE KYP verifier\n"
        "def ele_verify_kyp(ele_rows: list[int], ele_bound: int) -> bool:\n"
        "    ele_sum = 0\n"
        "    for ele_row in ele_rows:\n"
        "        ele_sum += ele_row * 73\n"
        "    return ele_sum <= ele_bound\n"
    )

    with tempfile.TemporaryDirectory(prefix="info_exp5_") as td:
        tdir = Path(td)
        p_ele = tdir / "ele.c"
        p_econ = tdir / "econ.c"
        p_unrel = tdir / "unrel.c"
        p_ele.write_text(c_ele, encoding="utf-8")
        p_econ.write_text(c_econ, encoding="utf-8")
        p_unrel.write_text(c_unrel, encoding="utf-8")

        j_clones = tdir / "ncd_clones.json"
        j_diff = tdir / "ncd_diff.json"
        assert (
            subprocess.run(
                [str(INFO_BIN), "alpha-ncd", str(p_ele), str(p_econ), "--lang", "c", "--out-json", str(j_clones)],
                capture_output=True,
                check=False,
            ).returncode
            == 0
        )
        assert (
            subprocess.run(
                [str(INFO_BIN), "alpha-ncd", str(p_ele), str(p_unrel), "--lang", "c", "--out-json", str(j_diff)],
                capture_output=True,
                check=False,
            ).returncode
            == 0
        )
        jc = json.loads(j_clones.read_text(encoding="utf-8"))
        jd = json.loads(j_diff.read_text(encoding="utf-8"))
        q12_b = 4096.0 * 8.0

        def ncd_pair(d: dict, pfx: str) -> float:
            la = d[f"{pfx}_la_q12"] / q12_b
            lb = d[f"{pfx}_lb_q12"] / q12_b
            lba = d[f"{pfx}_lba_q12"] / q12_b
            lab = d[f"{pfx}_lab_q12"] / q12_b
            return (min(la + lba, lb + lab) - min(la, lb)) / max(la, lb)

        raw_ncd_c = ncd_pair(jc, "raw")
        alpha_ncd_c = ncd_pair(jc, "alpha")
        alpha_ncd_d = ncd_pair(jd, "alpha")
        print(
            f"    C17 α-clones : raw_NCD={raw_ncd_c:.3f} -> alpha_NCD={alpha_ncd_c:.3f} "
            f"| unrelated alpha_NCD={alpha_ncd_d:.3f}"
        )
        assert alpha_ncd_c < raw_ncd_c, "Expected alpha_NCD < raw_NCD for renamed C17 clones"
        assert alpha_ncd_c < 0.25 and alpha_ncd_d > 0.70

        for ext, s1, s2 in [("lean", lean_1, lean_2), ("py", py_1, py_2)]:
            f1, f2 = tdir / f"a.{ext}", tdir / f"b.{ext}"
            c1, c2 = tdir / f"a.{ext}.canon", tdir / f"b.{ext}.canon"
            f1.write_text(s1, encoding="utf-8")
            f2.write_text(s2, encoding="utf-8")
            assert subprocess.run([str(INFO_BIN), "alpha-canon", str(f1), str(c1), "--lang", ext], check=False).returncode == 0
            assert subprocess.run([str(INFO_BIN), "alpha-canon", str(f2), str(c2), "--lang", ext], check=False).returncode == 0
            assert c1.read_bytes() == c2.read_bytes(), f"{ext} α-clones failed exact canonical collapse"

        # Joint ΔMDL: positive on clone group vs negative on unrelated shared module
        p_ele3 = tdir / "ele3.c"
        p_ele3.write_text(c_ele.replace("ele_", "phy_"), encoding="utf-8")
        j_pos, j_neg = tdir / "mdl_pos.json", tdir / "mdl_neg.json"
        assert (
            subprocess.run(
                [
                    str(INFO_BIN), "eval-mdl-group", "--alpha", "--lang", "c",
                    "--shared", str(p_ele), "--out-json", str(j_pos),
                    str(p_ele), str(p_econ), str(p_ele3),
                ],
                capture_output=True,
                check=False,
            ).returncode
            == 0
        )
        assert (
            subprocess.run(
                [
                    str(INFO_BIN), "eval-mdl-group", "--alpha", "--lang", "c",
                    "--shared", str(p_unrel), "--out-json", str(j_neg),
                    str(p_ele), str(p_econ),
                ],
                capture_output=True,
                check=False,
            ).returncode
            == 0
        )
        gp = json.loads(j_pos.read_text(encoding="utf-8"))["extract_gain_bits_q12"] / q12_b
        gn = json.loads(j_neg.read_text(encoding="utf-8"))["extract_gain_bits_q12"] / q12_b
        print(f"    Joint ΔMDL   : 3-clone gain={gp:+.1f} B (> 0) | unrelated gain={gn:+.1f} B (< 0)")
        assert gp > 0.0 and gn < 0.0

    # Verify noise/boilerplate classifier prevents false PR promotions
    tools_dir = str(ROOT / "tools")
    if tools_dir not in sys.path:
        sys.path.insert(0, tools_dir)
    from info_ecosystem_audit import classify_block_kind, classify_file_role  # type: ignore

    assert (
        classify_file_role(
            Path("include/ele.h"),
            "ELE/include/ele.h",
            "typedef struct { uint64_t magic; } EleAbi;\n#define ELE_MAGIC 1\n",
            "c",
        )
        == "abi_header"
    )
    assert (
        classify_file_role(
            Path("Phy.lean"),
            "PHY/Phy.lean",
            "def hdrLayout : CellLayout64 := CellLayout64.stdHeader64\n",
            "lean",
        )
        == "abi_header"
    )
    assert (
        classify_file_role(
            Path("oracles/verify_noether_oracle.py"),
            "PHY/oracles/verify_noether_oracle.py",
            "def verify(): return True\n",
            "py",
        )
        == "domain_oracle"
    )
    assert (
        classify_file_role(
            Path("experiments/exp1.py"),
            "INFO/experiments/exp1.py",
            "def run(): return 0\n",
            "py",
        )
        == "experiment_script"
    )
    assert (
        classify_file_role(
            Path("src/ele_cert.c"),
            "ELE/src/ele_cert.c",
            c_ele,
            "c",
        )
        == "logic"
    )
    table_src = "static const uint32_t lut[] = {\n" + "  0x01, 0x02, 0x03, 0x04,\n" * 10 + "};\n"
    assert classify_block_kind("PAINTER_LUT", table_src, "c", "logic") == "data_table"
    assert classify_block_kind("ele_mix_hash", c_ele, "c", "logic") == "logic"
    assert (
        classify_block_kind(
            "hdrLayout",
            "def hdrLayout : CellLayout64 := CellLayout64.stdHeader64",
            "lean",
            "abi_header",
        )
        == "schema_layout"
    )
    print("    Classifier   : abi_header / domain_oracle / experiment_script / data_table / logic PASS")


def run_part2_live_ecosystem() -> None:
    print("  --- Part 2: Live FLOW Ecosystem Cross-Repo MDL Audit ---")
    candidates = [
        ROOT.parent / "FLOW",
        ROOT.parent / "ELE",
        ROOT.parent / "CHEM",
        ROOT.parent / "QUA",
        ROOT.parent / "ECON",
        ROOT.parent / "PHY",
        ROOT.parent / "SOUND",
        ROOT,
    ]
    present = [p for p in candidates if p.is_dir()]
    with tempfile.TemporaryDirectory(prefix="info_live_audit_") as td:
        out_json = Path(td) / "audit.json"
        res = subprocess.run(
            [
                sys.executable,
                str(AUDIT_TOOL),
                "--roots",
                *[str(p) for p in present],
                "--top-pairs",
                "12",
                "--top-funcs",
                "10",
                "--out-json",
                str(out_json),
            ],
            cwd=str(ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        assert res.returncode == 0, f"Ecosystem audit failed: {res.stderr}\n{res.stdout}"
        print(res.stdout.rstrip())
        data = json.loads(out_json.read_text(encoding="utf-8"))
        assert data["files_indexed"] >= 10
        assert len(data["file_pairs"]) >= 1 or len(present) < 2
        assert "logic_clusters" in data and "filtered_clusters" in data
        assert "logic_func_clones" in data and "filtered_func_clones" in data
        assert data["clusters"] == data["logic_clusters"]
        assert "files" in data and all("role" in f for f in data["files"])


def main() -> int:
    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}"
    assert AUDIT_TOOL.is_file(), f"Missing {AUDIT_TOOL}"
    print("[Experiment 5] INFO v1.0.0 Structural α-Canonicalization & Ecosystem MDL Audit")
    run_part1_synthetic_ground_truth()
    run_part2_live_ecosystem()
    print("  [PASS] α-invariance, joint ΔMDL breakeven, and live cross-repo FLOW audit verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
