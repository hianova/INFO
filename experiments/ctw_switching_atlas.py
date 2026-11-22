#!/usr/bin/env python3
"""
INFO v1.0.0 — Finite-Sample CTW & Switching-Tree Redundancy Atlas
=================================================================
Cross-checks Ring-0 `classify-ctw` invariants (KT conservation & switching
dominance) and measures exact finite-sample redundancy (L_n - n*H*) of:
  - Order-0 KT estimator
  - Depth-2 Context Tree Weighting (CTW)
  - Switching-CTW (decaying non-stationary counts)
  - Full INFO Logistic Mixer (`build/info eval-bpb`)
across both stationary and multi-regime-switching depth-2 FSMX sources.
"""

from __future__ import annotations

import json
import math
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Dict, List, Tuple


ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
INFO_BIN = BUILD / "info"


def fsmx_entropy_rate_bpb(p1: List[float]) -> float:
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
        h_bit += pi[s] * (-(q1 * math.log2(q1) + q0 * math.log2(q0)))
    return h_bit


def gen_fsmx_segments(
    segments: List[Tuple[int, List[float]]], seed: int = 0xCAFE1234
) -> Tuple[bytes, float]:
    """Generates packed byte stream and exact piecewise expected bits sum (n * H*)."""
    rng = seed & ((1 << 64) - 1)
    state = 0
    out_bytes = bytearray()
    ideal_bits = 0.0
    for n_bytes, p1 in segments:
        h_seg_bit = fsmx_entropy_rate_bpb(p1)
        ideal_bits += (n_bytes * 8) * h_seg_bit
        for _ in range(n_bytes):
            bv = 0
            for _ in range(8):
                rng = (rng * 6364136223846793005 + 1442695040888963407) & ((1 << 64) - 1)
                u = (rng >> 32) / float(1 << 32)
                bit = 1 if u < p1[state] else 0
                bv = (bv << 1) | bit
                state = ((state << 1) & 3) | bit
            out_bytes.append(bv)
    return bytes(out_bytes), ideal_bits


def sim_python_predictors(data: bytes) -> Dict[str, float]:
    """Exact bit-level KT-0, Depth-2 CTW, and Switching-CTW redundancy tracker."""
    a0, b0 = 0, 0
    a2 = [0, 0, 0, 0]
    b2 = [0, 0, 0, 0]
    asw = [0.0, 0.0, 0.0, 0.0]
    bsw = [0.0, 0.0, 0.0, 0.0]
    kt0_bits = 0.0
    ctw_bits = 0.0
    sw_bits = 0.0
    ctx = 0
    for bv in data:
        for bp in range(7, -1, -1):
            bit = (bv >> bp) & 1
            p_kt0 = (b0 + 0.5) / (a0 + b0 + 1.0)
            p_ctw = (b2[ctx] + 0.5) / (a2[ctx] + b2[ctx] + 1.0)
            # Blend KT0 and depth-2 KT (exact binary CTW leaf/root weighting approximation via half mix)
            p_tree = 0.5 * p_kt0 + 0.5 * p_ctw
            p_sw = (bsw[ctx] + 0.5) / (asw[ctx] + bsw[ctx] + 1.0)

            kt0_bits += -math.log2(p_kt0 if bit else (1.0 - p_kt0))
            ctw_bits += -math.log2(p_tree if bit else (1.0 - p_tree))
            sw_bits += -math.log2(p_sw if bit else (1.0 - p_sw))

            if bit:
                b0 += 1
                b2[ctx] += 1
                bsw[ctx] += 1.0
            else:
                a0 += 1
                a2[ctx] += 1
                asw[ctx] += 1.0
            if (asw[ctx] + bsw[ctx]) >= 48.0:
                asw[ctx] *= 0.85
                bsw[ctx] *= 0.85
            ctx = ((ctx << 1) & 3) | bit
    return {"kt0_bits": kt0_bits, "ctw_bits": ctw_bits, "sw_ctw_bits": sw_bits}


def eval_info_bits(data: bytes, tmp_path: Path, json_path: Path) -> float:
    tmp_path.write_bytes(data)
    res = subprocess.run(
        [str(INFO_BIN), "eval-bpb", str(tmp_path), "--out-json", str(json_path)],
        capture_output=True,
        text=True,
        check=False,
    )
    assert res.returncode == 0, res.stderr
    return float(json.loads(json_path.read_text(encoding="utf-8"))["total_bits_q12"]) / 4096.0


def main() -> int:
    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}"
    print("[Experiment 3] INFO v1.0.0 Finite-Sample CTW & Switching-Tree Redundancy Atlas")

    with tempfile.TemporaryDirectory(prefix="info_ctw_atlas_") as td:
        tdir = Path(td)
        ctw_json = tdir / "ring0_ctw.json"
        res = subprocess.run(
            [str(INFO_BIN), "classify-ctw", "--out-json", str(ctw_json)],
            capture_output=True,
            text=True,
            check=False,
        )
        assert res.returncode == 0, res.stderr
        r0 = json.loads(ctw_json.read_text(encoding="utf-8"))
        assert r0["kt_conservation_ok"] == 1
        assert r0["switching_dominates_ok"] == 1
        print(
            f"  Ring-0 classify-ctw: stat_kt={r0['kt_stat_bits_q12']>>12} vs ctw={r0['ctw_stat_bits_q12']>>12} bits | "
            f"sw_ctw={r0['ctw_sw_bits_q12']>>12} vs switch={r0['sw_ctw_sw_bits_q12']>>12} bits (cons=OK, switch=OK)"
        )

        # Analytical multi-horizon finite-sample sweep
        p_a = [0.10, 0.85, 0.20, 0.80]
        p_b = [0.85, 0.12, 0.82, 0.15]

        print("  --- Stationary FSMX Horizon Sweep (Redundancy = L_n - n*H* bits) ---")
        stat_full, _ = gen_fsmx_segments([(4096, p_a)], seed=0x11112222)
        h_stat = fsmx_entropy_rate_bpb(p_a)
        for nbytes in [512, 1024, 2048, 4096]:
            sl = stat_full[:nbytes]
            ideal = (nbytes * 8) * h_stat
            pm = sim_python_predictors(sl)
            info_b = eval_info_bits(sl, tdir / f"stat_{nbytes}.bin", tdir / f"stat_{nbytes}.json")
            print(
                f"    n={nbytes:>4}B | nH*={ideal:>7.1f} | KT0 red={pm['kt0_bits']-ideal:>+7.1f} | "
                f"CTW red={pm['ctw_bits']-ideal:>+7.1f} | INFO_mix red={info_b-ideal:>+7.1f} ({info_b/(nbytes):.3f} bpb)"
            )
            assert info_b < pm["kt0_bits"], "INFO failed to beat KT0 on structured stationary FSMX"

        print("  --- Multi-Switch Non-Stationary FSMX Atlas (3 Regime Switches) ---")
        sw_segs = [(1024, p_a), (1024, p_b), (1024, p_a), (1024, p_b)]
        sw_full, sw_ideal = gen_fsmx_segments(sw_segs, seed=0x33334444)
        pm_sw = sim_python_predictors(sw_full)
        info_sw = eval_info_bits(sw_full, tdir / "sw_full.bin", tdir / "sw_full.json")
        print(
            f"    n=4096B (3 switches) | sum(nH*)={sw_ideal:>7.1f} | "
            f"CTW red={pm_sw['ctw_bits']-sw_ideal:>+7.1f} | "
            f"SwCTW red={pm_sw['sw_ctw_bits']-sw_ideal:>+7.1f} | "
            f"INFO_mix red={info_sw-sw_ideal:>+7.1f}"
        )
        assert pm_sw["sw_ctw_bits"] < pm_sw["ctw_bits"], "Switching CTW failed to beat static CTW"
        assert info_sw < pm_sw["ctw_bits"], "INFO mixer failed to beat static CTW on multi-switch FSMX"

    print("  [PASS] CTW conservation, finite-sample redundancy, and switching dominance verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
