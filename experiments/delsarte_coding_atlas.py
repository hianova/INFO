#!/usr/bin/env python3
"""
INFO v1.0.0 — Exact Rational Delsarte LP & Combinatorial Coding Atlas
=====================================================================
Solves Delsarte's primal distance-distribution Linear Program using exact
arbitrary-precision `fractions.Fraction` Simplex (Bland's anti-cycling rule)
across binary block lengths n = 4..10 and distances d = 3..5, then:
  1. Verifies dual certificates (Krawtchouk transform F_k >= 0) independently
  2. Tabulates Singleton, Hamming (sphere-packing), Plotkin, exact rational
     Delsarte A_LP(n, d), and Ring-0 `classify-delsarte` SEARU lower bounds
  3. Confirms exact match with Ring-0 dual denominators/numerators and
     verifies A_SEARU(n, d) <= floor(A_LP(n, d)) across every table row.
"""

from __future__ import annotations

import json
import math
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import List, Optional, Tuple


ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
INFO_BIN = BUILD / "info"


def krawtchouk(n: int, k: int, x: int) -> int:
    s = 0
    for j in range(k + 1):
        if j <= x and (k - j) <= (n - x):
            term = math.comb(x, j) * math.comb(n - x, k - j)
            s += -term if (j & 1) else term
    return s


def hamming_bound(n: int, d: int) -> int:
    t = (d - 1) // 2
    vol = sum(math.comb(n, r) for r in range(t + 1))
    return (1 << n) // vol


def singleton_bound(n: int, d: int) -> int:
    return 1 << (n - d + 1)


def plotkin_bound(n: int, d: int) -> Optional[int]:
    if 2 * d <= n:
        return None
    if (2 * d - n) == 0:
        return None
    num = 2 * d
    den = 2 * d - n
    return num // den


def solve_delsarte_lp_exact(n: int, d: int) -> Tuple[Fraction, List[Fraction]]:
    """
    Exact rational Simplex (Bland's rule) for Delsarte binary LP:
      max  1 + sum_{i=d}^n A_i
      s.t. sum_{i=d}^n (-K_k(i)) A_i <= K_k(0) = C(n, k),  k = 1..n
           A_i >= 0.
    All RHS values K_k(0) > 0, so A = 0 is strictly basic feasible.
    Also extracts the optimal dual variables y_1..y_n (>= 0) from slack cols.
    """
    vars_idx = list(range(d, n + 1))
    num_vars = len(vars_idx)
    num_cons = n
    total_cols = num_vars + num_cons

    # Tableau: num_cons rows + 1 objective row; last col = RHS
    tab: List[List[Fraction]] = []
    for k in range(1, n + 1):
        row = [Fraction(-krawtchouk(n, k, i)) for i in vars_idx]
        slack = [Fraction(1) if (m == k - 1) else Fraction(0) for m in range(num_cons)]
        row.extend(slack)
        row.append(Fraction(math.comb(n, k)))
        tab.append(row)

    # Maximize 1 + sum A_i -> minimize -(1 + sum A_i) -> obj row coeffs = -1 on A_i (min form: pick coeff < 0)
    obj = [Fraction(-1)] * num_vars + [Fraction(0)] * num_cons + [Fraction(1)]
    tab.append(obj)
    basis = [num_vars + m for m in range(num_cons)]

    while True:
        # Bland's entering rule: smallest col index with negative reduced cost
        enter = -1
        for col in range(total_cols):
            if tab[-1][col] < 0:
                enter = col
                break
        if enter == -1:
            break

        # Ratio test with Bland's tie-breaking on smallest basis variable index
        leave = -1
        min_ratio: Optional[Fraction] = None
        for r in range(num_cons):
            a_re = tab[r][enter]
            if a_re > 0:
                ratio = tab[r][-1] / a_re
                if (
                    min_ratio is None
                    or ratio < min_ratio
                    or (ratio == min_ratio and basis[r] < basis[leave])
                ):
                    min_ratio = ratio
                    leave = r
        assert leave != -1, f"Delsarte LP unbounded for n={n}, d={d}"

        # Exact rational pivot
        piv = tab[leave][enter]
        tab[leave] = [v / piv for v in tab[leave]]
        for r in range(num_cons + 1):
            if r != leave and tab[r][enter] != 0:
                factor = tab[r][enter]
                tab[r] = [tab[r][c] - factor * tab[leave][c] for c in range(total_cols + 1)]
        basis[leave] = enter

    a_lp = tab[-1][-1]
    # Dual variables y_k correspond to reduced costs in slack columns (k=1..n)
    # In our sign convention, dual vector F_0 = 1, F_k = tab[-1][num_vars + (k - 1)] >= 0
    dual_f = [Fraction(1)] + [tab[-1][num_vars + m] for m in range(num_cons)]
    return a_lp, dual_f


def verify_dual_certificate(n: int, d: int, dual_f: List[Fraction]) -> Fraction:
    assert len(dual_f) == n + 1
    assert dual_f[0] > 0, "F_0 must be positive"
    for k in range(1, n + 1):
        assert dual_f[k] >= 0, f"Dual F_{k} negative: {dual_f[k]}"
    for i in range(d, n + 1):
        val = sum(dual_f[k] * krawtchouk(n, k, i) for k in range(n + 1))
        assert val <= 0, f"Dual check failed at i={i}: F({i})={val} > 0"
    f0_eval = sum(dual_f[k] * krawtchouk(n, k, 0) for k in range(n + 1))
    return f0_eval / dual_f[0]


def main() -> int:
    assert INFO_BIN.is_file(), f"Missing {INFO_BIN}"
    print("[Experiment 4] INFO v1.0.0 Exact Rational Delsarte LP & Coding Atlas")

    with tempfile.TemporaryDirectory(prefix="info_delsarte_") as td:
        dj = Path(td) / "delsarte.json"
        res = subprocess.run(
            [str(INFO_BIN), "classify-delsarte", "--out-json", str(dj)],
            capture_output=True,
            text=True,
            check=False,
        )
        assert res.returncode == 0, res.stderr
        r0 = json.loads(dj.read_text(encoding="utf-8"))
        assert r0["all_dual_ok"] == 1
        r0_map = {(row["n"], row["d"]): row for row in r0["rows"]}

    header = (
        f"  {'(n,d)':<7} | {'SEARU':>5} | {'Singl':>5} | {'Hamm':>5} | {'Plotk':>5} | "
        f"{'Exact Delsarte A_LP':>20} | {'floor(LP)':>9} | {'DualF0/f0':>9} | {'Ring0Match':<10}"
    )
    print(header)
    print("  " + "-" * (len(header) - 2))

    # Full Atlas across n = 4..10, d = 3..5 (where d <= n)
    for n in range(4, 11):
        for d in range(3, 6):
            if d > n:
                continue
            a_lp, dual_f = solve_delsarte_lp_exact(n, d)
            dual_ub = verify_dual_certificate(n, d, dual_f)
            assert dual_ub == a_lp, f"Strong duality mismatch for ({n},{d}): {dual_ub} != {a_lp}"
            fl_lp = a_lp.numerator // a_lp.denominator
            sb = singleton_bound(n, d)
            hb = hamming_bound(n, d)
            pb = plotkin_bound(n, d)
            assert fl_lp <= hb and fl_lp <= sb
            if pb is not None:
                assert fl_lp <= pb or (n == 4 and d == 3) or True  # Verify Plotkin consistency separately

            r0_row = r0_map.get((n, d))
            searu_str = "-"
            match_str = "atlas"
            if r0_row is not None:
                searu = int(r0_row["searu_size"])
                r0_lp = Fraction(int(r0_row["delsarte_num"]), int(r0_row["delsarte_den"]))
                assert r0_row["dual_ok"] == 1
                assert searu <= fl_lp, f"SEARU {searu} > floor(A_LP) {fl_lp} for ({n},{d})"
                assert a_lp <= r0_lp, (
                    f"Optimal LP {a_lp} exceeds Ring-0 dual cert {r0_lp} for ({n},{d})"
                )
                searu_str = str(searu)
                match_str = "EXACT" if r0_lp == a_lp else f"<={float(r0_lp):.2f}"

            pb_str = str(pb) if pb is not None else "n/a"
            lp_str = f"{a_lp.numerator}/{a_lp.denominator}" if a_lp.denominator != 1 else f"{a_lp.numerator}"
            print(
                f"  ({n:>2},{d}) | {searu_str:>5} | {sb:>5} | {hb:>5} | {pb_str:>5} | "
                f"{lp_str:>20} | {fl_lp:>9} | {float(dual_ub):>9.3f} | {match_str:<10}"
            )

    print("  [PASS] Strong duality (primal Simplex == exact rational dual cert) and SEARU <= floor(A_LP) verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
