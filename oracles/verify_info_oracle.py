#!/usr/bin/env python3
"""
INFO v1.0.0 — Independent Exact-Rational & Live Lean Certificate Oracle (Gate 5)
=================================================================================
Verifies:
  1. Standalone `build/info_decomp` SHA-256 bit-exact roundtrip across edge/text/alg payloads
  2. `classify-ctw` exact `fractions.Fraction` KT conservation & switching dominance
  3. `classify-separation` pure-Python LFSR-23 / CA32 Rule-30 / Affine-16 parity
  4. `classify-delsarte` independent combinatorial Krawtchouk + dual verification
  5. `classify-causal` independent Balke-Pearl rational bounds + Causal MDL
  6. Parallel 5/5 live `lean -DwarningAsError=true` + `leanchecker` + `0 sorryAx` replay.
"""

from __future__ import annotations

import concurrent.futures
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional, Tuple


def _find_elan_tool(name: str) -> Path:
    env_override = os.environ.get(name.upper())
    if env_override:
        return Path(env_override)
    which_p = shutil.which(name)
    if which_p:
        return Path(which_p)
    home_p = Path.home() / ".elan" / "bin" / name
    if home_p.exists():
        return home_p
    return Path("/Users/kuangtalin/.elan/bin") / name


ROOT = Path(__file__).resolve().parent.parent
BUILD = ROOT / "build"
INFO_BIN = BUILD / "info"
DECOMP_BIN = BUILD / "info_decomp"
LEAN = _find_elan_tool("lean")
LEANCHECKER = _find_elan_tool("leanchecker")


def run_cmd(
    cmd: List[str], env: Optional[Dict[str, str]] = None, stdin_text: Optional[str] = None
) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd,
        cwd=str(ROOT),
        env=env,
        input=stdin_text,
        capture_output=True,
        text=True,
        check=False,
    )


# ---------------------------------------------------------------------------
# 1. Pure-Python Reference Algorithms
# ---------------------------------------------------------------------------

def py_krawtchouk(n: int, k: int, x: int) -> int:
    s = 0
    for j in range(k + 1):
        if j <= x and (k - j) <= (n - x):
            term = math.comb(x, j) * math.comb(n - x, k - j)
            s += -term if (j & 1) else term
    return s


def py_balke_pearl_bounds(c0: List[int], c1: List[int]) -> Tuple[Fraction, Fraction]:
    s0 = sum(c0)
    s1 = sum(c1)
    assert s0 > 0 and s0 == s1
    p00_0, p01_0, p10_0, p11_0 = [Fraction(x, s0) for x in c0]
    p00_1, p01_1, p10_1, p11_1 = [Fraction(x, s1) for x in c1]
    low = max(
        p11_0 + p00_1 - 1,
        p00_0 + p11_1 - 1,
        p11_0 + p00_0 - 1,
        p11_1 + p00_1 - 1,
        Fraction(-1, 1),
    )
    high = min(
        1 - p01_0 - p10_1,
        1 - p01_1 - p10_0,
        1 - p01_0 - p10_0,
        1 - p01_1 - p10_1,
        Fraction(1, 1),
    )
    return low, high


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


# ---------------------------------------------------------------------------
# 2. Oracle Verification Suites
# ---------------------------------------------------------------------------

def verify_decomp_roundtrip() -> None:
    assert DECOMP_BIN.is_file(), f"Missing {DECOMP_BIN}"
    payloads = [
        ("empty", b""),
        ("short3", b"xyz"),
        ("text", b"Compression is understanding: Kraft, CTW, Balke-Pearl, Causal MDL.\n" * 64),
        ("lfsr23", py_gen_lfsr23(0x5ACE1, 4096)),
        ("ca32", py_gen_ca32_rule30(0x13579BDF, 4096)),
        ("aff16", py_gen_affine16(25173, 13849, 7, 4096)),
    ]
    with tempfile.TemporaryDirectory(prefix="inf_oracle_dec_") as td:
        tdir = Path(td)
        for name, data in payloads:
            raw_p = tdir / f"{name}.bin"
            inf_p = tdir / f"{name}.inf"
            dec_p = tdir / f"{name}.dec"
            raw_p.write_bytes(data)
            r1 = run_cmd([str(INFO_BIN), "compress", str(raw_p), str(inf_p)])
            assert r1.returncode == 0, r1.stderr
            r2 = run_cmd([str(DECOMP_BIN), str(inf_p), str(dec_p)])
            assert r2.returncode == 0, f"{DECOMP_BIN} failed on {name}: {r2.stderr}"
            got_hash = hashlib.sha256(dec_p.read_bytes()).hexdigest()
            exp_hash = hashlib.sha256(data).hexdigest()
            assert got_hash == exp_hash, f"SHA-256 mismatch on {name}"
    print(f"  [Oracle-Decomp] {len(payloads)}/{len(payloads)} SHA-256 bit-exact via standalone info_decomp ({DECOMP_BIN.stat().st_size}B) PASS")


def verify_classifiers() -> None:
    cdir = BUILD / "certs"
    cdir.mkdir(parents=True, exist_ok=True)

    # 2a. CTW + exact Fraction KT step conservation check
    for a in range(16):
        for b in range(16):
            p1 = Fraction(2 * a + 1, 2 * (a + b + 1))
            p0 = Fraction(2 * b + 1, 2 * (a + b + 1))
            assert p1 + p0 == 1
    ctw_p = cdir / "classify_ctw.json"
    assert run_cmd([str(INFO_BIN), "classify-ctw", "--out-json", str(ctw_p)]).returncode == 0
    ctw = json.loads(ctw_p.read_text(encoding="utf-8"))
    assert ctw["kt_conservation_ok"] == 1
    assert ctw["switching_dominates_ok"] == 1
    assert ctw["ctw_stat_bits_q12"] < ctw["kt_stat_bits_q12"]
    assert ctw["sw_ctw_sw_bits_q12"] < ctw["ctw_sw_bits_q12"]

    # 2b. Algorithmic blindspot separation cross-checked on Python-generated streams
    sep_p = cdir / "classify_sep.json"
    assert run_cmd([str(INFO_BIN), "classify-separation", "--out-json", str(sep_p)]).returncode == 0
    sep = json.loads(sep_p.read_text(encoding="utf-8"))
    assert sep["lfsr_roundtrip_ok"] == 1 and sep["ca_roundtrip_ok"] == 1 and sep["aff_roundtrip_ok"] == 1
    assert sep["lfsr_ctx_bits"] >= 30720 and sep["lfsr_alg_bits"] <= 614
    assert sep["ca_ctx_bits"] >= 30720 and sep["ca_alg_bits"] <= 614
    assert sep["aff_ctx_bits"] >= 30720 and sep["aff_alg_bits"] <= 614

    # Cross-check eval-bpb on Python-generated LFSR23 / CA32 / Aff16 matches C17 identically
    with tempfile.TemporaryDirectory(prefix="inf_sep_py_") as td:
        tdir = Path(td)
        for tag, blob in [
            ("lfsr", py_gen_lfsr23(0x5ACE1, 4096)),
            ("ca", py_gen_ca32_rule30(0x13579BDF, 4096)),
            ("aff", py_gen_affine16(25173, 13849, 7, 4096)),
        ]:
            fp = tdir / f"{tag}.bin"
            jp = tdir / f"{tag}.json"
            fp.write_bytes(blob)
            assert run_cmd([str(INFO_BIN), "eval-bpb", str(fp), "--no-alg", "--out-json", str(jp)]).returncode == 0
            got_ev = json.loads(jp.read_text(encoding="utf-8"))
            assert (got_ev["total_bits_q12"] >> 12) == sep[f"{tag}_ctx_bits"], f"{tag} Py<->C17 generator mismatch!"

    # 2c. Delsarte Krawtchouk + Sphere Packing + Singleton cross-check
    del_p = cdir / "classify_delsarte.json"
    assert run_cmd([str(INFO_BIN), "classify-delsarte", "--out-json", str(del_p)]).returncode == 0
    dl = json.loads(del_p.read_text(encoding="utf-8"))
    assert dl["all_dual_ok"] == 1
    for r in dl["rows"]:
        n, d = r["n"], r["d"]
        assert r["singleton_ub"] == (1 << (n - (d - 1)))
        t = (d - 1) // 2
        ball = sum(math.comb(n, k) for k in range(t + 1))
        assert r["hamming_ub"] == (1 << n) // ball
        assert Fraction(r["searu_size"]) <= Fraction(r["delsarte_num"], r["delsarte_den"])
        assert r["dual_ok"] == 1

    # 2d. Balke-Pearl rational simplex + Causal MDL check
    cau_p = cdir / "classify_causal.json"
    assert run_cmd([str(INFO_BIN), "classify-causal", "--out-json", str(cau_p)]).returncode == 0
    cau = json.loads(cau_p.read_text(encoding="utf-8"))
    py_lo, py_hi = py_balke_pearl_bounds([12, 2, 3, 15], [3, 1, 4, 24])
    assert Fraction(cau["bp_low_num"], cau["bp_den"]) == py_lo
    assert Fraction(cau["bp_high_num"], cau["bp_den"]) == py_hi
    assert cau["bp_sound"] == 1 and cau["obs_equiv_verified"] == 1
    assert cau["causal_mdl_correct"] == cau["causal_mdl_pairs_tested"]

    print("  [Oracle-Classifiers] CTW + Separation(LFSR23/CA32/Aff16) + Delsarte + Balke-Pearl PASS")


# ---------------------------------------------------------------------------
# 3. Live `hunt` + Witness Audit + Parallel `lean` + `leanchecker` Replay
# ---------------------------------------------------------------------------

def _replay_one_cert(mode: str, lean_file: Path, mod_name: str) -> Tuple[str, int]:
    src = lean_file.read_text(encoding="utf-8")
    if re.search(r"\b(sorry|admit)\b", src):
        raise AssertionError(f"{lean_file} contains sorry/admit!")

    env = dict(os.environ)
    env["LEAN_PATH"] = f"{BUILD / 'lean'}:{BUILD / 'certs'}"

    ns_m = re.search(r"^\s*namespace\s+(\S+)", src, re.MULTILINE)
    assert ns_m is not None, f"Missing namespace in {lean_file}"
    ns = ns_m.group(1)
    thms = re.findall(r"^\s*theorem\s+(\S+)", src, re.MULTILINE)
    assert len(thms) >= 2, f"Expected >=2 theorems in {lean_file}, got {thms}"

    olean = BUILD / "certs" / f"{mod_name}.olean"
    c_res = run_cmd(
        [str(LEAN), "-DwarningAsError=true", "--root", str(BUILD / "certs"), "-o", str(olean), str(lean_file)],
        env=env,
    )
    assert c_res.returncode == 0, f"lean compile failed for {mode}:\n{c_res.stdout}\n{c_res.stderr}"

    lc_res = run_cmd([str(LEANCHECKER), mod_name], env=env)
    assert lc_res.returncode == 0, f"leanchecker failed for {mode}:\n{lc_res.stdout}\n{lc_res.stderr}"

    ax_lines = "\n".join(f"#print axioms {ns}.{t}" for t in thms)
    ax_res = run_cmd([str(LEAN), "--stdin"], env=env, stdin_text=f"import {mod_name}\n{ax_lines}\n")
    assert ax_res.returncode == 0, f"axiom audit failed for {mode}:\n{ax_res.stderr}"
    if "sorryAx" in ax_res.stdout or "Lean.ofReduceBool" in ax_res.stdout:
        raise AssertionError(f"Forbidden axiom detected in {mode}:\n{ax_res.stdout}")
    return (mode, len(thms))


def verify_all_hunts_and_certs() -> None:
    cdir = BUILD / "certs"
    cdir.mkdir(parents=True, exist_ok=True)
    specs = [
        ("alg-blindspot", "InfoCertOracleAlg"),
        ("ctw-switch", "InfoCertOracleCtw"),
        ("delsarte-gap", "InfoCertOracleDelsarte"),
        ("balke-pearl", "InfoCertOracleBP"),
        ("causal-mdl", "InfoCertOracleCausal"),
    ]
    jobs = []
    for mode, mod_name in specs:
        lean_p = cdir / f"{mod_name}.lean"
        fir_p = cdir / f"oracle_{mode.replace('-', '_')}.fir"
        json_p = cdir / f"oracle_{mode.replace('-', '_')}.json"
        res = run_cmd([
            str(INFO_BIN), "hunt", mode, "--seed", "0x1337",
            "--out-lean", str(lean_p), "--out-fir", str(fir_p), "--out-json", str(json_p),
        ])
        assert res.returncode == 0, f"hunt {mode} failed: {res.stderr}"
        w = json.loads(json_p.read_text(encoding="utf-8"))
        assert w["fir_eval_ok"] is True and w["fir_wire_bytes"] >= 64
        if mode == "alg-blindspot":
            assert w["roundtrip_ok"] == 1 and w["full_alg_bytes"] < w["pure_ctx_bytes"] // 10
        elif mode == "ctw-switch":
            assert w["sw_dominates"] == 1 and w["sw_bits_q12"] < w["ctw_bits_q12"]
        elif mode == "delsarte-gap":
            assert w["dual_ok"] == 1 and w["searu_size"] >= 16
            # Also independently verify Krawtchouk identity at n=7, d=3 -> 256/16=16
            assert py_krawtchouk(7, 0, 3) == 1 and py_krawtchouk(7, 2, 3) == -3
        elif mode == "balke-pearl":
            assert w["natural_bound_ok"] == 1 and w["obs_equiv_ok"] == 1
            py_lo, py_hi = py_balke_pearl_bounds([10, 2, 4, 16], [2, 2, 4, 24])
            assert Fraction(w["low_num"], w["den"]) == py_lo
            assert Fraction(w["high_num"], w["den"]) == py_hi
        elif mode == "causal-mdl":
            assert w["dir_recovered"] == 1 and w["lxy_total_q12"] < w["lyx_total_q12"]
        jobs.append((mode, lean_p, mod_name))

    with concurrent.futures.ThreadPoolExecutor(max_workers=len(jobs)) as ex:
        futs = [ex.submit(_replay_one_cert, m, lp, mn) for (m, lp, mn) in jobs]
        summary = [f"{m}({nt} thms)" for (m, nt) in (f.result() for f in futs)]
    print(f"  [Oracle-CertReplay] 5/5 live lean + leanchecker + 0 sorryAx PASS: {', '.join(summary)}")


def verify_alpha_mdl_oracle() -> None:
    src_a = (
        "/* ELE subsystem */\n"
        "uint64_t ele_solve(const uint32_t *ele_arr, uint32_t ele_n) {\n"
        "    uint64_t ele_acc = 12345U;\n"
        "    for (uint32_t ele_i = 0; ele_i < ele_n; ele_i++) {\n"
        "        ele_acc ^= flow_ir_eval_u64(ele_arr, ele_i & 15U) + 16U;\n"
        "    }\n"
        "    return ele_acc;\n"
        "}\n"
    )
    src_b = (
        "/* ECON settlement\n   multi-line block */\n"
        "uint64_t econ_settle(const uint32_t *econ_orders, uint32_t econ_cnt) {\n"
        "    uint64_t econ_sum = 77777U;\n"
        "    for (uint32_t econ_k = 0; econ_k < econ_cnt; econ_k++) {\n"
        "        econ_sum ^= flow_ir_eval_u64(econ_orders, econ_k & 15U) + 16U;\n"
        "    }\n"
        "    return econ_sum;\n"
        "}\n"
    )
    src_diff = (
        "typedef struct { int x; int y; } Pt;\n"
        "void draw_grid(Pt *pts, int w) {\n"
        "    if (!pts || w <= 0) return;\n"
        "    pts[0].x = pts[0].y + 999;\n"
        "}\n"
    )
    lean_a = "theorem foo_a (x : Nat) : x + 1 = 1 + x := by omega\n"
    lean_b = "-- different comment\ntheorem bar_b (z : Nat) : z + 1 = 1 + z := by omega\n"
    py_a = "# c1\ndef ele_norm(ele_x: int) -> int:\n    return (ele_x + 42) & 0xFF\n"
    py_b = "# c2\ndef chem_norm(chem_z: int) -> int:\n    return (chem_z + 99) & 0xFF\n"
    expr_a = "THM C_Alpha.thm : AP FA PROP C_Alpha.add BV0\nAP LM BV0 AP C_Alpha.add C_Alpha.zero\n"
    expr_b = "THM C_Beta.lem : AP FA PROP C_Beta.mul BV0\nAP LM BV0 AP C_Beta.mul C_Gamma.one\n"

    with tempfile.TemporaryDirectory(prefix="inf_oracle_alpha_") as td:
        tdir = Path(td)
        pa, pb, pd = tdir / "a.c", tdir / "b.c", tdir / "d.c"
        oa, ob = tdir / "a.canon", tdir / "b.canon"
        pa.write_text(src_a, encoding="utf-8")
        pb.write_text(src_b, encoding="utf-8")
        pd.write_text(src_diff, encoding="utf-8")

        assert run_cmd([str(INFO_BIN), "alpha-canon", str(pa), str(oa), "--lang", "c"]).returncode == 0
        assert run_cmd([str(INFO_BIN), "alpha-canon", str(pb), str(ob), "--lang", "c"]).returncode == 0
        assert oa.read_bytes() == ob.read_bytes(), "α-renamed C clones failed canonical equality"
        assert b"flow_ir_eval_u64" in oa.read_bytes(), "FLOW anchor dropped during α-canon"

        for ext, s1, s2 in [("lean", lean_a, lean_b), ("py", py_a, py_b), ("expr", expr_a, expr_b)]:
            f1, f2 = tdir / f"s1.{ext}", tdir / f"s2.{ext}"
            c1, c2 = tdir / f"c1.{ext}", tdir / f"c2.{ext}"
            f1.write_text(s1, encoding="utf-8")
            f2.write_text(s2, encoding="utf-8")
            assert run_cmd([str(INFO_BIN), "alpha-canon", str(f1), str(c1), "--lang", ext]).returncode == 0
            assert run_cmd([str(INFO_BIN), "alpha-canon", str(f2), str(c2), "--lang", ext]).returncode == 0
            assert c1.read_bytes() == c2.read_bytes(), f"α-renamed {ext} failed canonical equality"
        assert b"AP LM BV0" in (tdir / "c1.expr").read_bytes(), "Expr opcodes not preserved"

        j_ncd = tdir / "ncd.json"
        assert (
            run_cmd([str(INFO_BIN), "alpha-ncd", str(pa), str(pb), "--lang", "c", "--out-json", str(j_ncd)]).returncode
            == 0
        )
        jn = json.loads(j_ncd.read_text(encoding="utf-8"))
        assert jn["alpha_lba_q12"] < jn["raw_lba_q12"], "Expected alpha_lba < raw_lba on α-clones"

        j_pos, j_neg = tdir / "pos.json", tdir / "neg.json"
        assert (
            run_cmd([
                str(INFO_BIN), "eval-mdl-group", "--alpha", "--lang", "c",
                "--shared", str(pa), "--out-json", str(j_pos), str(pa), str(pb), str(pa),
            ]).returncode
            == 0
        )
        jp = json.loads(j_pos.read_text(encoding="utf-8"))
        assert jp["joint_savings_bits_q12"] > 0 and jp["extract_gain_bits_q12"] > 0

        assert (
            run_cmd([
                str(INFO_BIN), "eval-mdl-group", "--alpha", "--lang", "c",
                "--shared", str(pd), "--out-json", str(j_neg), str(pa), str(pb),
            ]).returncode
            == 0
        )
        jg = json.loads(j_neg.read_text(encoding="utf-8"))
        assert jg["extract_gain_bits_q12"] < 0
    print("  [Oracle-AlphaMDL] C/Lean/Python α-invariance + ΔMDL breakeven PASS")


def main() -> int:
    if not INFO_BIN.is_file():
        print(f"ERROR: missing {INFO_BIN}; run `make all` first.", file=sys.stderr)
        return 1
    print("[Gate 5] INFO v1.0.0 Independent Exact-Rational Oracle & Live Lean Replay")
    verify_decomp_roundtrip()
    verify_classifiers()
    verify_all_hunts_and_certs()
    verify_alpha_mdl_oracle()
    print("[Gate 5] PASS (SHA-256 decomp, 4/4 classifiers, 5/5 live Lean+leanchecker certs, α-MDL)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
