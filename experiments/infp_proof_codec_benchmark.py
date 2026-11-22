#!/usr/bin/env python3
"""
INFO v1.0.0 — Experiment 7: Lossless .infp Proof-DAG Codec & Cognitive Transparency MDL Bridge
==============================================================================================
Part 1 (2-Repo CI-Portable Lossless Lean Proof-DAG Compression):
  Exports full hash-consed `Lean.Environment` kernel `Expr` DAGs via
  `tools/lean_expr_export.lean export-dag`, packs them through sparse transposed
  columns + Ring-0 `./build/info compress` into 48B-header `.infp` containers,
  decompresses via standalone zero-heap `./build/info_decomp` (34,072 B), and
  verifies 100% SHA-256 bit-exact reconstruction across `Info.Theory`, `Flow.Math`,
  and any compiled sibling `.olean` libraries present locally.

Part 2 (INFO x SOUND Cognitive Transparency MDL Bridge):
  Measures standalone and summary-conditioned MDL (`./build/info eval-bpb` and
  `./build/info ncd`) across a plain-language disclosure summary `S`, a transparent
  fair contract `C_fair`, and a labyrinthine cross-referenced predatory contract
  `C_pred`, empirically instantiating Theorem 15 (`cognitive_transparency_mdl_bound`).
"""

from __future__ import annotations

import gzip
import json
import lzma
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


ROOT = Path(__file__).resolve().parent.parent
INFO_BIN = ROOT / "build" / "info"
DECOMP_BIN = ROOT / "build" / "info_decomp"
EXPORT_SCRIPT = ROOT / "tools" / "lean_expr_export.lean"
TOOLS_DIR = ROOT / "tools"
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

from info_lean_distill import find_lean_bin  # type: ignore  # noqa: E402
from info_proof_codec import (  # type: ignore  # noqa: E402
    INFP_VERSION_1,
    INFP_VERSION_2,
    canonical_dag_bytes,
    canonical_dag_sha256,
    pack_dag_to_infp,
    unpack_infp_to_dag,
)


SUMMARY_PROSE = """Plain-Language Consumer Investment Disclosure (1-Page Summary)
==============================================================
Product: Elder Capital Preservation Plan (Fixed Principal Account)
Custodian: Civic Trust Bank N.A. | Customer: Senior Depositor

Key Binding Commitments Disclosed Before Signing:
1. Principal Protection: 100% of deposited principal ($25,000) is protected at maturity and upon qualifying notice.
2. Early Withdrawal Cap: The customer may withdraw funds at any time with 30 days written notice; total exit fee never exceeds $1,000.
3. Liability Ceiling: Total customer obligation or termination fee under all scenarios combined shall never exceed $25,000 maximum liability, with fixed interest at 3.25% APR.
4. Dispute Resolution: Disputes remain eligible for local small-claims or public civil court; no mandatory secret arbitration fee-shifting applies.
5. Amendment Protection: No unilateral interest reset, hidden annex override, or default forfeiture multiplier may alter these four guarantees.
6. Clear Plain-Text Schedule: Annual statement issued in plain language 60 days prior to any renewal option.
"""

FAIR_CONTRACT = """Elder Capital Preservation Agreement (Transparent Bilateral Contract)
===================================================================
Article 1 — Protected Principal Account ($25,000):
  CustodianCivic Trust Bank N.A. holds 100% of Customer principal ($25,000) in a segregated preservation account earning 3.25% APR simple interest, paid quarterly.

Article 2 — Early Withdrawal & Redemption Cap (30-Day Written Notice):
  Customer may withdraw any portion of deposited principal with 30 days written notice. Total administrative exit fee shall never exceed $1,000 in aggregate, regardless of market rate movements.

Article 3 — Total Liability Ceiling ($25,000 Cap):
  Across all scenarios, notices, and administrative charges combined, Customer's aggregate obligation and fee exposure never exceeds $25,000. No multiplier, liquidated damage penalty, or default acceleration applies.

Article 4 — Judicial Venue & Immunity Against Unilateral Overrides:
  Disputes remain within local civil or small-claims court at Customer's election. Custodian has no unilateral power to impose secret arbitration fee-shifting, retroactively reset interest below 3.25% APR, or waive statutory elder consumer immunities.

Article 5 — Annual Plain-Language Renewal Notice:
  Renewal never occurs silently: Custodian issues a plain-language notice 60 days prior to maturity, preserving Customer's 30-day withdrawal right and $1,000 exit fee cap.
"""

PREDATORY_CONTRACT = """MASTER INSTITUTIONAL ASSET ALLOCATION & DEFERRED FIDUCIARY INDENTURE (REV. 2026-K9)
====================================================================================================
SECTION 1. DEFINITIONS & HIERARCHICAL PRECEDENCE OF ANNEXES.
1.1 "Disclosed Benefit Cap" means $25,000 only during the Introductory Window defined in Schedule Z-9(c).
1.2 Notwithstanding Section 1.1 and any Oral or Plain-Language Summary dated prior to execution, pursuant to Subsection 14(b)(iii) and Annex Omega Clause 38.4, Institutional Discretion shall govern all Allocation Events.
SECTION 2. INTRODUCTORY PRINCIPAL ACKNOWLEDGMENT.
2.1 Subject to Recalculation under Sections 9, 17, 23, and 34, Depositor transfers Initial Tranche ($25,000).
SECTION 3. CONDITIONAL WITHDRAWAL PRIVILEGE.
3.1 Except as suspended during a Volatility Trigger (Section 19.2) or Liquidity Freeze (Section 27.1), requests require Form-B9 notarization plus Annex Q clearance.
SECTION 4. CROSS-DEFAULT & CONTINGENT INDEMNITY BRIDGE.
4.1 Any delay exceeding seventy-two (72) hours in custodial documentation constitutes a Technical Default Event under Section 18(a), activating Cumulative Multiplier Tier III of 2.85x Principal Assessment.
SECTION 5. INTEREST RESET & NEGATIVE CONVEXITY ADJUSTMENT.
5.1 Where Reference Interbank Spreads diverge by >= 15 bps, Yield switches retroactively from 3.25% to -1.75% Deferred Custody Fee deducted monthly from corpus under Sub-clause 11(d)(ii).
SECTION 6. SURRENDER SCHEDULE & DEFERRED ORIGINATION RECAPTURE.
6.1 Redemption prior to Month 120 incurs Surrender Charge of $4,500 plus Recapture Fee of 18% plus Market-Value-Adjustment (Annex M Formula 7: max(0, (R_spot - R_orig) * D_rem * 1.45)).
SECTION 7. MANDATORY ARBITRAL TRIBUNAL & BILATERAL VENUE WAIVER.
7.1 Depositor irrevocably waives jury trial, class action, and local small-claims access; all claims exceeding $500 must be filed before Private Arbiter Panel in Delaware with non-refundable $6,500 filing retainer borne by Depositor regardless of outcome.
SECTION 8. INCORPORATION BY REFERENCE OF DYNAMIC ONLINE SCHEDULES.
8.1 Bank may amend Annex Alpha through Annex Omega via electronic bulletin posting under URL Policy 404-B; continued non-objection for five (5) business days constitutes binding Novation.
SECTION 9. DEFEASIBLE PRIORITY & EXCEPTION-TO-EXCEPTION CASCADE.
9.1 If Section 3.1 would cap Fees at $1,000, Section 6.1 overrides Section 3.1 unless Section 4.1 already triggered Multiplier Tier III, in which case Section 18(c) Superseding Lien attaches to joint family accounts.
SECTION 10. SECONDARY FEE ESCROW & MARGIN REPLENISHMENT.
10.1 Should Corpus dip below 85% via Section 5.1 deductions or Section 6.1 Market-Value-Adjustment, Depositor shall remit Margin Call Cure within 48 hours or suffer Foreclosure Auction Discount of 35%.
SECTION 11. TAX GROSS-UP & FIDUCIARY IMMUNITY CARVE-OUT.
11.1 Depositor indemnifies Custodian against administrative inquiries, regulatory audits, and legal fees on a solicitor-and-client basis under Clause 31.7 without reciprocity.
SECTION 12. CONFESSION OF JUDGMENT & AUTOMATED DEBIT AUTHORIZATION.
12.1 Custodian holds durable power-of-attorney limited to ACH sweeps across linked checking balances under Routing Mandate Annex F whenever Unbilled Penalty Ledger exceeds $250.
SECTION 13-22. [NESTED OVERRIDE MATRIX CLAUSES 13.1-22.9]
  Clause 13.4 subjects Clause 2.1 to Annex D haircut; Clause 14.2(b) nullifies notice protections upon non-standard holiday calendar variance; Clause 15.8 imposes $1,200 Quarterly Compliance Surcharge; Clause 16.3 subordinates depositor priority under Senior Repo Carve-Out; Clause 17.5 converts uncollected fees into 24% APR Compounded Arrears Notes; Clause 18.9 disallows set-off by Depositor while preserving Unconditional Bank Set-off; Clause 19.6 extends freeze duration indefinitely; Clause 20.1 bars oral evidence under Parol Integration Merger; Clause 21.3 shifts FX conversion spreads of 475 bps; Clause 22.8 triggers Acceleration Fee upon account holder incapacitation or probate filing ($12,500 Estate Administration Levy).
SECTION 23-40. [CHISHOLM PENALTY CASCADE & ENTIRE AGREEMENT OVERRIDES]
  Annex Omega Clause 38.4 supersedes Section 1.1, Section 2.1, Section 3.1, and any Summary Sheet in entirety; Severability Clause 39.2 preserves all fee-shifting covenants even if principal guarantee is voided under Clause 40.9 ("Nothing herein creates a fiduciary duty toward Depositor").
"""


def measure_olean_family_bytes(root_path: str, mod: str, prefix: str) -> int:
    """Sum .olean sizes matching the exported library prefix for fair disk comparison."""
    total = 0
    for item in root_path.split(":"):
        p = Path(item)
        if not p.is_dir():
            continue
        sub = p / prefix
        if sub.is_dir():
            for ol in sub.rglob("*.olean"):
                total += ol.stat().st_size
        top = p / f"{prefix}.olean"
        if top.is_file():
            total += top.stat().st_size
        mod_file = p / (mod.replace(".", "/") + ".olean")
        if mod_file.is_file() and sub not in mod_file.parents and mod_file != top:
            total += mod_file.stat().st_size
    return total


def run_zstd_19(data_path: Path) -> Optional[int]:
    if shutil.which("zstd") is None:
        return None
    res = subprocess.run(
        ["zstd", "-19", "-q", "-c", str(data_path)],
        capture_output=True,
        check=False,
    )
    if res.returncode != 0:
        return None
    return len(res.stdout)


def run_part1_infp_codec_benchmark() -> None:
    print("  --- Part 1: Lossless .infp Proof-DAG Codec Benchmark (SHA-256 Bit-Exact via info_decomp) ---")
    lean_bin = find_lean_bin()
    candidates: List[Tuple[str, str, str, Path]] = [
        (
            "Info.Theory",
            "Info",
            str(ROOT / "build" / "lean"),
            ROOT / "build" / "lean" / "Info" / "Theory.olean",
        ),
        (
            "Flow.Math",
            "Flow",
            str(ROOT.parent / "FLOW" / "build" / "lean"),
            ROOT.parent / "FLOW" / "build" / "lean" / "Flow" / "Math.olean",
        ),
        (
            "Sound.Theory",
            "Sound",
            str(ROOT.parent / "SOUND" / "build" / "lean"),
            ROOT.parent / "SOUND" / "build" / "lean" / "Sound" / "Theory.olean",
        ),
        (
            "Phy.Noether",
            "Phy",
            f"{ROOT.parent / 'PHY' / 'build' / 'lean'}:{ROOT.parent / 'FLOW' / 'build' / 'lean'}",
            ROOT.parent / "PHY" / "build" / "lean" / "Phy" / "Noether.olean",
        ),
        (
            "EleCert",
            "EleCert",
            f"{ROOT.parent / 'FLOW' / 'build' / 'lean'}:{ROOT.parent / 'ELE' / 'build'}",
            ROOT.parent / "ELE" / "build" / "EleCert.olean",
        ),
        (
            "EconCert",
            "EconCert",
            f"{ROOT.parent / 'FLOW' / 'build' / 'lean'}:{ROOT.parent / 'ECON' / 'build'}",
            ROOT.parent / "ECON" / "build" / "EconCert.olean",
        ),
        (
            "ChemCert",
            "ChemCert",
            f"{ROOT.parent / 'FLOW' / 'build' / 'lean'}:{ROOT.parent / 'CHEM' / 'build'}",
            ROOT.parent / "CHEM" / "build" / "ChemCert.olean",
        ),
    ]

    audited = 0
    with tempfile.TemporaryDirectory(prefix="info_exp7_dag_") as td:
        tdir = Path(td)
        for mod, pfx, lpath, olean in candidates:
            if not olean.is_file():
                continue
            dag_path = tdir / f"{mod}.dag.json"
            infp1_path = tdir / f"{mod}.v1.infp"
            infp2_path = tdir / f"{mod}.v2.infp"
            env = os.environ.copy()
            env["LEAN_PATH"] = lpath
            res = subprocess.run(
                [lean_bin, "--run", str(EXPORT_SCRIPT), "export-dag", mod, pfx, str(dag_path), lpath],
                cwd=str(ROOT),
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            assert res.returncode == 0, f"export-dag failed for {mod}: {res.stderr}"

            raw_bytes = dag_path.read_bytes()
            dag = json.loads(raw_bytes.decode("utf-8"))
            stats = dag["stats"]
            assert stats["decl_count"] > 0 and stats["global_dag_nodes"] > 0
            assert stats["total_tree_nodes"] >= stats["global_dag_nodes"]

            orig_sha = canonical_dag_sha256(dag).hex()
            gz_bytes = len(gzip.compress(raw_bytes, compresslevel=9))
            lzma_bytes = len(lzma.compress(raw_bytes, preset=9))
            zstd_bytes = run_zstd_19(dag_path)
            olean_bytes = measure_olean_family_bytes(lpath, mod, pfx)

            m1 = pack_dag_to_infp(dag, infp1_path, INFO_BIN, len(raw_bytes), version=INFP_VERSION_1)
            d1, s1 = unpack_infp_to_dag(infp1_path, DECOMP_BIN)
            assert s1 == orig_sha and d1["stats"] == stats

            m2 = pack_dag_to_infp(dag, infp2_path, INFO_BIN, len(raw_bytes), version=INFP_VERSION_2)
            d2, s2 = unpack_infp_to_dag(infp2_path, DECOMP_BIN)
            assert s2 == orig_sha and d2["stats"] == stats

            assert m2["infp_bytes"] < m1["infp_bytes"] < lzma_bytes < gz_bytes < len(raw_bytes), (
                f"{mod}: v2={m2['infp_bytes']} v1={m1['infp_bytes']} lzma9={lzma_bytes} gz9={gz_bytes}"
            )

            zstd_str = f"{zstd_bytes:>7}" if zstd_bytes is not None else "    n/a"
            ratio_v2 = len(raw_bytes) / m2["infp_bytes"]
            print(
                f"    {mod:<13} | olean={olean_bytes:>9}B | json={len(raw_bytes):>7}B | "
                f"lzma9={lzma_bytes:>6}B zstd19={zstd_str}B | v1={m1['infp_bytes']:>6}B -> "
                f"v2={m2['infp_bytes']:>6}B ({ratio_v2:>5.2f}x, macros={m2['hot_macro_count']:>4}) | SHA256=EXACT"
            )
            audited += 1

        # Explicitly exercise multi-chunk .infp v2 roundtrip via unmodified 34,072 B info_decomp
        info_dag = json.loads((tdir / "Info.Theory.dag.json").read_text(encoding="utf-8"))
        info_sha = canonical_dag_sha256(info_dag).hex()
        chunked_p = tdir / "Info.Theory.chunked.infp"
        mc = pack_dag_to_infp(info_dag, chunked_p, INFO_BIN, version=INFP_VERSION_2, chunk_size=65536)
        assert mc["num_chunks"] >= 2, mc
        dec_mc, sha_mc = unpack_infp_to_dag(chunked_p, DECOMP_BIN)
        assert sha_mc == info_sha and dec_mc["stats"] == info_dag["stats"]
        print(
            f"    [Chunked v2] Info.Theory: chunks={mc['num_chunks']} (64KiB), "
            f"size={mc['infp_bytes']}B, SHA256={sha_mc[:12]}.. EXACT via 34,072B info_decomp"
        )

    flow_olean = ROOT.parent / "FLOW" / "build" / "lean" / "Flow" / "Math.olean"
    assert audited >= (2 if flow_olean.is_file() else 1)


def run_part2_kernel_retypecheck_roundtrip() -> None:
    print("  --- Part 2: Standalone .infp v2 -> info_decomp -> Lean Kernel Re-typecheck (0 Target .olean) ---")
    lean_bin = find_lean_bin()
    info_lean_dir = ROOT / "build" / "lean"
    with tempfile.TemporaryDirectory(prefix="info_exp7_kreplay_") as td:
        tdir = Path(td)

        # Case A: Info.Causal verified inside pure `Init` kernel with empty LEAN_PATH!
        raw_c = tdir / "causal_full.json"
        infp_c = tdir / "causal_full.infp"
        dec_c = tdir / "causal_decoded.json"
        env_exp = os.environ.copy()
        env_exp["LEAN_PATH"] = str(info_lean_dir)
        r_exp = subprocess.run(
            [
                lean_bin, "--run", str(EXPORT_SCRIPT), "export-dag", "--with-internal-deps",
                "Info.Causal", "Info.Causal", str(raw_c), str(info_lean_dir),
            ],
            cwd=str(ROOT), env=env_exp, capture_output=True, text=True, check=False,
        )
        assert r_exp.returncode == 0, r_exp.stderr
        dag_c = json.loads(raw_c.read_text(encoding="utf-8"))
        sha_c = canonical_dag_sha256(dag_c).hex()
        m_c = pack_dag_to_infp(dag_c, infp_c, INFO_BIN, raw_c.stat().st_size, version=INFP_VERSION_2)
        dec_dag_c, dec_sha_c = unpack_infp_to_dag(infp_c, DECOMP_BIN)
        assert dec_sha_c == sha_c and "induct_groups" in dec_dag_c
        dec_c.write_bytes(canonical_dag_bytes(dec_dag_c))

        env_empty = os.environ.copy()
        env_empty["LEAN_PATH"] = ""
        r_ver_c = subprocess.run(
            [lean_bin, "--run", str(EXPORT_SCRIPT), "verify-dag", str(dec_c), "Init"],
            cwd=str(ROOT), env=env_empty, capture_output=True, text=True, check=False,
        )
        assert r_ver_c.returncode == 0 and "KERNEL PASS" in r_ver_c.stdout, r_ver_c.stdout + r_ver_c.stderr
        print(
            f"    Info.Causal   | json={raw_c.stat().st_size:>6}B -> .infp v2={m_c['infp_bytes']:>5}B | "
            f"{r_ver_c.stdout.strip()}"
        )

        # Case B: Info.ProofMDL verified against ONLY Info.Coding.olean (ProofMDL.olean physically absent!)
        iso_lean = tdir / "isolated_lean"
        (iso_lean / "Info").mkdir(parents=True, exist_ok=True)
        shutil.copy2(info_lean_dir / "Info" / "Coding.olean", iso_lean / "Info" / "Coding.olean")
        assert not (iso_lean / "Info" / "ProofMDL.olean").exists()

        raw_p = tdir / "pmdl_full.json"
        infp_p = tdir / "pmdl_full.infp"
        dec_p = tdir / "pmdl_decoded.json"
        r_exp2 = subprocess.run(
            [
                lean_bin, "--run", str(EXPORT_SCRIPT), "export-dag", "--with-internal-deps",
                "Info.ProofMDL", "Info.ProofMDL", str(raw_p), str(info_lean_dir),
            ],
            cwd=str(ROOT), env=env_exp, capture_output=True, text=True, check=False,
        )
        assert r_exp2.returncode == 0, r_exp2.stderr
        dag_p = json.loads(raw_p.read_text(encoding="utf-8"))
        sha_p = canonical_dag_sha256(dag_p).hex()
        m_p = pack_dag_to_infp(dag_p, infp_p, INFO_BIN, raw_p.stat().st_size, version=INFP_VERSION_2)
        dec_dag_p, dec_sha_p = unpack_infp_to_dag(infp_p, DECOMP_BIN)
        assert dec_sha_p == sha_p
        dec_p.write_bytes(canonical_dag_bytes(dec_dag_p))

        env_iso = os.environ.copy()
        env_iso["LEAN_PATH"] = str(iso_lean)
        r_ver_p = subprocess.run(
            [lean_bin, "--run", str(EXPORT_SCRIPT), "verify-dag", str(dec_p), "Info.Coding", str(iso_lean)],
            cwd=str(ROOT), env=env_iso, capture_output=True, text=True, check=False,
        )
        assert r_ver_p.returncode == 0 and "KERNEL PASS" in r_ver_p.stdout, r_ver_p.stdout + r_ver_p.stderr
        print(
            f"    Info.ProofMDL | json={raw_p.stat().st_size:>6}B -> .infp v2={m_p['infp_bytes']:>5}B | "
            f"{r_ver_p.stdout.strip()}"
        )


def run_eval_bpb(path: Path, out_json: Path) -> Dict[str, Any]:
    res = subprocess.run(
        [str(INFO_BIN), "eval-bpb", str(path), "--out-json", str(out_json)],
        capture_output=True,
        text=True,
        check=False,
    )
    assert res.returncode == 0, res.stderr
    return json.loads(out_json.read_text(encoding="utf-8"))


def run_ncd(path_a: Path, path_b: Path, out_json: Path) -> Dict[str, Any]:
    res = subprocess.run(
        [str(INFO_BIN), "ncd", str(path_a), str(path_b), "--out-json", str(out_json)],
        capture_output=True,
        text=True,
        check=False,
    )
    assert res.returncode == 0, res.stderr
    return json.loads(out_json.read_text(encoding="utf-8"))


def compute_ncd_ratio(ncd_json: Dict[str, Any]) -> float:
    la = int(ncd_json["la_bits_q12"])
    lb = int(ncd_json["lb_bits_q12"])
    lb_given_a = int(ncd_json["lb_given_a_bits_q12"])
    la_given_b = int(ncd_json["la_given_b_bits_q12"])
    c_joint = min(la + lb_given_a, lb + la_given_b)
    return float(c_joint - min(la, lb)) / float(max(la, lb))


def run_part3_cognitive_transparency_bridge() -> None:
    print("  --- Part 3: INFO x SOUND Cognitive Transparency MDL Bridge ---")
    with tempfile.TemporaryDirectory(prefix="info_exp7_cog_") as td:
        tdir = Path(td)
        p_sum = tdir / "summary.txt"
        p_fair = tdir / "fair_contract.txt"
        p_pred = tdir / "labyrinth_contract.txt"
        p_sum.write_text(SUMMARY_PROSE, encoding="utf-8")
        p_fair.write_text(FAIR_CONTRACT, encoding="utf-8")
        p_pred.write_text(PREDATORY_CONTRACT, encoding="utf-8")

        ev_sum = run_eval_bpb(p_sum, tdir / "ev_sum.json")
        ev_fair = run_eval_bpb(p_fair, tdir / "ev_fair.json")
        ev_pred = run_eval_bpb(p_pred, tdir / "ev_pred.json")

        ncd_fair = run_ncd(p_sum, p_fair, tdir / "ncd_fair.json")
        ncd_pred = run_ncd(p_sum, p_pred, tdir / "ncd_pred.json")

        fair_cond_bits = int(ncd_fair["lb_given_a_bits_q12"])
        pred_cond_bits = int(ncd_pred["lb_given_a_bits_q12"])
        fair_ncd = compute_ncd_ratio(ncd_fair)
        pred_ncd = compute_ncd_ratio(ncd_pred)
        fair_total = int(ev_fair["total_bits_q12"])
        pred_total = int(ev_pred["total_bits_q12"])

        assert fair_cond_bits < pred_cond_bits, f"{fair_cond_bits} >= {pred_cond_bits}"
        assert fair_ncd < pred_ncd, f"{fair_ncd} >= {pred_ncd}"
        assert fair_total < pred_total, f"{fair_total} >= {pred_total}"

        sum_b = int(ev_sum["total_bits_q12"]) / (4096.0 * 8.0)
        fair_b = fair_total / (4096.0 * 8.0)
        pred_b = pred_total / (4096.0 * 8.0)
        fair_cb = fair_cond_bits / (4096.0 * 8.0)
        pred_cb = pred_cond_bits / (4096.0 * 8.0)

        print(
            f"    Summary S ({int(ev_sum['orig_bytes'])}B)       : C(S)={sum_b:.1f} B"
        )
        print(
            f"    Fair C_fair ({int(ev_fair['orig_bytes'])}B)     : C(C_fair)={fair_b:.1f} B | "
            f"C(C_fair|S)={fair_cb:.1f} B | NCD={fair_ncd:.4f}"
        )
        print(
            f"    Labyrinth C_pred ({int(ev_pred['orig_bytes'])}B): C(C_pred)={pred_b:.1f} B | "
            f"C(C_pred|S)={pred_cb:.1f} B | NCD={pred_ncd:.4f}"
        )


def main() -> int:
    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}"
    assert DECOMP_BIN.is_file(), f"Missing {DECOMP_BIN}"
    print("[Experiment 7] INFO v1.0.0 Lossless .infp v2 Proof-DAG Codec, Kernel Replay & Cognitive Transparency Bridge")
    run_part1_infp_codec_benchmark()
    run_part2_kernel_retypecheck_roundtrip()
    run_part3_cognitive_transparency_bridge()
    print("  [PASS] 100% SHA-256 .infp v2 Proof-DAG roundtrip (via info_decomp), standalone Kernel Replay & Cognitive MDL Bridge verified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
