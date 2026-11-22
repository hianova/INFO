#!/usr/bin/env python3
"""
tools/info_sabotage_check.py — 36-Mutant Single-Fault Sabotage Gate (Gate 6)
===============================================================================
Verifies 100.0% mutation-kill efficacy (36/36 killed, 0 compile errors) across
12 categories (3 mutants each) in `src/info_ring0.c`:
   1. arith_coder          (3)
   2. stretch_squash       (3)
   3. context_models       (3)
   4. match_model          (3)
   5. logistic_mixer       (3)
   6. alg_lfsr_bm          (3)
   7. alg_affine_ca        (3)
   8. inf1_framing         (3)
   9. ctw_switch           (3)
  10. delsarte_krawtchouk  (3)
  11. balke_pearl_bounds   (3)
  12. causal_mdl_surprise  (3)
"""

from __future__ import annotations

import concurrent.futures
import os
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class InfoMutant:
    name: str
    category: str
    target: str
    replacement: str


def build_info_mutants() -> list[InfoMutant]:
    return [
        # --- 1. arith_coder (3) ---
        InfoMutant(
            "M01_ac_enc_wrong_interval",
            "arith_coder",
            "    if (bit != 0U) {\n        e->high = mid;\n    } else {\n        e->low = mid + UINT32_C(1);\n    }",
            "    if (bit == 0U) {\n        e->high = mid;\n    } else {\n        e->low = mid + UINT32_C(1);\n    }",
        ),
        InfoMutant(
            "M02_ac_enc_drop_e3_pending",
            "arith_coder",
            "        } else if (e->low >= INFO_AC_Q1 && e->high < INFO_AC_Q3) {\n"
            "            e->pending++;\n"
            "            e->low = (e->low - INFO_AC_Q1) << 1U;",
            "        } else if (e->low >= INFO_AC_Q1 && e->high < INFO_AC_Q3) {\n"
            "            e->low = (e->low - INFO_AC_Q1) << 1U;",
        ),
        InfoMutant(
            "M03_ac_dec_e3_drop_q1_shift",
            "arith_coder",
            "        } else if (d->low >= INFO_AC_Q1 && d->high < INFO_AC_Q3) {\n"
            "            d->low = (d->low - INFO_AC_Q1) << 1U;\n"
            "            d->high = ((d->high - INFO_AC_Q1) << 1U) | UINT32_C(1);\n"
            "            d->code = ((d->code - INFO_AC_Q1) << 1U) | ac_get_raw_bit(d);",
            "        } else if (d->low >= INFO_AC_Q1 && d->high < INFO_AC_Q3) {\n"
            "            d->low = d->low << 1U;\n"
            "            d->high = (d->high << 1U) | UINT32_C(1);\n"
            "            d->code = (d->code << 1U) | ac_get_raw_bit(d);",
        ),
        # --- 2. stretch_squash (3) ---
        InfoMutant(
            "M04_stretch_zero_lower_clamp",
            "stretch_squash",
            "    if (p <= 1U) {\n        return (int32_t)k_stretch_nodes[0];\n    }",
            "    if (p <= 1U) {\n        return 0;\n    }",
        ),
        InfoMutant(
            "M05_squash_saturate_half",
            "stretch_squash",
            "    if (x >= 2048) {\n        return UINT32_C(4095);\n    }",
            "    if (x >= 2048) {\n        return UINT32_C(2048);\n    }",
        ),
        InfoMutant(
            "M06_neg_log2_invert_interp",
            "stretch_squash",
            "    uint32_t diff = y0 - y1;\n    uint32_t res = y0 - ((diff * rem) >> 4U);",
            "    uint32_t diff = y0 - y1;\n    uint32_t res = y0 + ((diff * rem) >> 4U);",
        ),
        # --- 3. context_models (3) ---
        InfoMutant(
            "M07_ord0_freeze_probability",
            "context_models",
            "    *slot = (uint16_t)((p_new << 4U) | cnt);\n"
            "    return p_new;",
            "    *slot = (uint16_t)((p << 4U) | cnt);\n"
            "    (void)p_new;\n"
            "    return p;",
        ),
        InfoMutant(
            "M08_tagged_lookup_return_half",
            "context_models",
            "    if ((uint16_t)(entry >> 16U) == tag) {\n"
            "        uint32_t p = (entry >> 4U) & UINT32_C(4095);\n"
            "        return (p < 1U) ? UINT32_C(2048) : ((p > 4095U) ? UINT32_C(4095) : p);\n"
            "    }",
            "    if ((uint16_t)(entry >> 16U) == tag) {\n"
            "        (void)entry;\n"
            "        return UINT32_C(2048);\n"
            "    }",
        ),
        InfoMutant(
            "M09_tagged_update_drop_store",
            "context_models",
            "    tbl[idx] = ((uint32_t)tag << 16U) | (p_new << 4U) | cnt;",
            "    (void)tbl;\n    (void)idx;\n    (void)tag;\n    (void)p_new;\n    (void)cnt;",
        ),
        # --- 4. match_model (3) ---
        InfoMutant(
            "M10_match_disable_probe",
            "match_model",
            "                    st->match_pos = cand;\n                    st->match_len = UINT32_C(4);",
            "                    st->match_pos = cand;\n                    st->match_len = UINT32_C(0);",
        ),
        InfoMutant(
            "M11_match_invert_logit",
            "match_model",
            "        int32_t mag = (st->match_len >= 16U) ? 1800 : (600 + (int32_t)st->match_len * 75);\n"
            "        m_logit = (exp_b != 0U) ? mag : -mag;",
            "        int32_t mag = (st->match_len >= 16U) ? 1800 : (600 + (int32_t)st->match_len * 75);\n"
            "        m_logit = (exp_b == 0U) ? mag : -mag;",
        ),
        InfoMutant(
            "M12_match_drop_mismatch_cancel",
            "match_model",
            "        if (bit != exp_b) {\n            st->match_len = UINT32_C(0);\n        }",
            "        if (bit != exp_b && false) {\n            st->match_len = UINT32_C(0);\n        }",
        ),
        # --- 5. logistic_mixer (3) ---
        InfoMutant(
            "M13_mixer_zero_dot_product",
            "logistic_mixer",
            "    for (uint32_t k = 0U; k < INFO_WS_NUM_EXPERTS; k++) {\n"
            "        dot += (int64_t)ws->mix_w[st->mix_ctx][k] * (int64_t)st->logits[k];\n"
            "    }",
            "    for (uint32_t k = 0U; k < INFO_WS_NUM_EXPERTS; k++) {\n"
            "        (void)ws;\n"
            "    }",
        ),
        InfoMutant(
            "M14_mixer_freeze_sgd_weights",
            "logistic_mixer",
            "            ws->mix_w[st->mix_ctx][k] =\n"
            "                info_clamp_i32(ws->mix_w[st->mix_ctx][k] + dw, -8192, 16384);",
            "            ws->mix_w[st->mix_ctx][k] = 0;\n            (void)dw;",
        ),
        InfoMutant(
            "M15_sse_drop_blend",
            "logistic_mixer",
            "    uint32_t p_out = (p_mix + p_sse * UINT32_C(3)) >> 2U;",
            "    (void)p_sse;\n    uint32_t p_out = UINT32_C(2048);",
        ),
        # --- 6. alg_lfsr_bm (3) ---
        InfoMutant(
            "M16_bm_drop_poly_xor",
            "alg_lfsr_bm",
            "            if (st->bm_m < 40U) {\n                st->bm_c ^= (st->bm_b << st->bm_m);\n            }",
            "            if (st->bm_m < 40U) {\n                (void)t_poly;\n            }",
        ),
        InfoMutant(
            "M17_bm_invert_lfsr_pred",
            "alg_lfsr_bm",
            "        if (st->bm_streak >= 12U && st->bm_l > 0U && st->bm_l <= 24U) {\n"
            "            uint32_t l_pred = info_parity64(st->bit_hist64 & (st->bm_c >> 1U));\n"
            "            alg_logit = (l_pred != 0U) ? 1950 : -1950;\n"
            "            alg_locked = UINT32_C(1);",
            "        if (st->bm_streak >= 12U && st->bm_l > 0U && st->bm_l <= 24U) {\n"
            "            uint32_t l_pred = info_parity64(st->bit_hist64 & (st->bm_c >> 1U));\n"
            "            alg_logit = (l_pred == 0U) ? 1950 : -1950;\n"
            "            alg_locked = UINT32_C(1);",
        ),
        InfoMutant(
            "M18_alg_drop_hit_counter",
            "alg_lfsr_bm",
            "    if (alg_locked != 0U) {\n        st->alg_hits++;\n    }",
            "    if (alg_locked != 0U) {\n        st->alg_hits = UINT64_C(0);\n    }",
        ),
        # --- 7. alg_affine_ca (3) ---
        InfoMutant(
            "M19_aff16_truncate_hensel",
            "alg_affine_ca",
            "                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &\n"
            "                          UINT32_C(0xFFFF);\n"
            "                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &\n"
            "                          UINT32_C(0xFFFF);\n"
            "                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &\n"
            "                          UINT32_C(0xFFFF);\n"
            "                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &\n"
            "                          UINT32_C(0xFFFF);",
            "                    inv = UINT32_C(1);",
        ),
        InfoMutant(
            "M20_ca32_corrupt_center_nb",
            "alg_affine_ca",
            "                uint32_t nb = (((w_cur32 >> l_bit) & 1U) << 2U) | (((w_cur32 >> bit) & 1U) << 1U) |\n"
            "                              ((w_cur32 >> r_bit) & 1U);",
            "                uint32_t nb = (((w_cur32 >> l_bit) & 1U) << 2U) | ((w_cur32 >> r_bit) & 1U);\n"
            "                (void)bit;",
        ),
        InfoMutant(
            "M21_ca32_freeze_streak",
            "alg_affine_ca",
            "                st->ca32_rule_mask = r32;\n"
            "                st->ca32_known_mask = k32;\n"
            "                st->ca32_streak++;",
            "                st->ca32_rule_mask = r32;\n"
            "                st->ca32_known_mask = k32;\n"
            "                st->ca32_streak = UINT32_C(0);",
        ),
        # --- 8. inf1_framing (3) ---
        InfoMutant(
            "M22_inf1_corrupt_magic_write",
            "inf1_framing",
            "    info_put_u32_le(dst, INFO_INF1_MAGIC);",
            "    info_put_u32_le(dst, INFO_INF1_MAGIC ^ UINT32_C(1));",
        ),
        InfoMutant(
            "M23_inf1_bypass_magic_check",
            "inf1_framing",
            "    if (magic != INFO_INF1_MAGIC || (size_t)orig_sz > dst_cap) {\n"
            "        return SIZE_MAX;\n"
            "    }",
            "    if ((size_t)orig_sz > dst_cap) {\n"
            "        (void)magic;\n"
            "        return SIZE_MAX;\n"
            "    }",
        ),
        InfoMutant(
            "M24_inf1_bypass_fnv32_check",
            "inf1_framing",
            "    if (got_fnv32 != exp_fnv32) {\n        return SIZE_MAX;\n    }",
            "    if (got_fnv32 != exp_fnv32 && false) {\n        return SIZE_MAX;\n    }",
        ),
        # --- 9. ctw_switch (3) ---
        InfoMutant(
            "M25_ctw_ignore_tree_ctx",
            "ctw_switch",
            "        uint32_t id = use_tree ? ctx2 : UINT32_C(0);",
            "        (void)use_tree;\n        uint32_t id = UINT32_C(0);",
        ),
        InfoMutant(
            "M26_ctw_disable_switch_decay",
            "ctw_switch",
            "        if (use_switch && (a[id] + b[id]) >= 32U) {\n"
            "            a[id] >>= 1U;\n"
            "            b[id] >>= 1U;\n"
            "        }",
            "        if (false && use_switch && (a[id] + b[id]) >= 32U) {\n"
            "            a[id] >>= 1U;\n"
            "            b[id] >>= 1U;\n"
            "        }",
        ),
        InfoMutant(
            "M27_ctw_force_cons_fail",
            "ctw_switch",
            "    out->kt_conservation_ok = cons_ok ? UINT32_C(1) : UINT32_C(0);",
            "    (void)cons_ok;\n    out->kt_conservation_ok = UINT32_C(0);",
        ),
        # --- 10. delsarte_krawtchouk (3) ---
        InfoMutant(
            "M28_krawtchouk_drop_alt_sign",
            "delsarte_krawtchouk",
            "            if ((j & 1U) != 0U) {\n                sum -= term;\n            } else {\n                sum += term;\n            }",
            "            sum += term;",
        ),
        InfoMutant(
            "M29_delsarte_corrupt_7_3_den",
            "delsarte_krawtchouk",
            "        *ub_num = 256U;\n        *ub_den = 16U;",
            "        *ub_num = 256U;\n        *ub_den = 15U;",
        ),
        InfoMutant(
            "M30_searu_code_cap_one",
            "delsarte_krawtchouk",
            "        for (uint32_t idx = 0U; idx < max_v && cur_sz < 32U; idx++) {",
            "        for (uint32_t idx = 0U; idx < max_v && cur_sz < 1U; idx++) {",
        ),
        # --- 11. balke_pearl_bounds (3) ---
        InfoMutant(
            "M31_bp_inflate_lower_bound",
            "balke_pearl_bounds",
            "    int64_t l_cands[8] = {p11_0 + p00_1 - S,",
            "    int64_t l_cands[8] = {p11_0 + p00_1 + S,",
        ),
        InfoMutant(
            "M32_bp_invert_interval_ends",
            "balke_pearl_bounds",
            "    *low_num = lo;\n    *high_num = hi;",
            "    *low_num = hi + 1;\n    *high_num = lo - 1;",
        ),
        InfoMutant(
            "M33_bp_deflate_upper_bound",
            "balke_pearl_bounds",
            "    int64_t u_cands[8] = {\n        S - p01_0 - p10_1,",
            "    int64_t u_cands[8] = {\n        -S - p01_0 - p10_1,",
        ),
        # --- 12. causal_mdl_surprise (3) ---
        InfoMutant(
            "M34_causal_icm_zero_mechanism",
            "causal_mdl_surprise",
            "        uint8_t yv = (uint8_t)((mag * mag) >> 2U);",
            "        uint8_t yv = UINT8_C(0);",
        ),
        InfoMutant(
            "M35_surprise_drop_spike_track",
            "causal_mdl_surprise",
            "        if (i >= 16U && byte_q12 > max_b_surp) {\n"
            "            max_b_surp = byte_q12;\n"
            "            spike_off = (uint64_t)i;\n"
            "        }",
            "        if (false && i >= 16U && byte_q12 > max_b_surp) {\n"
            "            max_b_surp = byte_q12;\n"
            "            spike_off = (uint64_t)i;\n"
            "        }",
        ),
        InfoMutant(
            "M36_causal_mdl_invert_direction",
            "causal_mdl_surprise",
            "        if (total_fwd < total_rev) {\n            ok_cnt++;\n        }",
            "        if (total_fwd > total_rev) {\n            ok_cnt++;\n        }",
        ),
        # --- 13. alpha_mdl_canon (3) ---
        InfoMutant(
            "M37_alpha_disable_id_norm",
            "alpha_mdl_canon",
            "    if (id < INFO_ALPHA_MAX_IDS) {\n"
            "        static const uint8_t k_hex[16] = {'0', '1', '2', '3', '4', '5', '6', '7',\n"
            "                                          '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'};\n"
            "        uint8_t buf[3];\n"
            "        buf[0] = (uint8_t)'V';\n"
            "        buf[1] = k_hex[((uint32_t)id >> 4U) & UINT32_C(0xF)];\n"
            "        buf[2] = k_hex[(uint32_t)id & UINT32_C(0xF)];\n"
            "        alpha_emit_slice(w, buf, 3U);\n"
            "    } else {\n"
            "        alpha_emit_cstr(w, \"VX\");\n"
            "    }",
            "    (void)id;\n"
            "    alpha_emit_slice(w, tok, len);",
        ),
        InfoMutant(
            "M38_alpha_drop_comment_strip",
            "alpha_mdl_canon",
            "        if (lang == INFO_LANG_C && ch == (uint8_t)'/' && i + 1U < src_len) {\n"
            "            if (src[i + 1U] == (uint8_t)'*') {",
            "        if (lang == INFO_LANG_C && ch == (uint8_t)'/' && i + 1U < src_len) {\n"
            "            if (src[i + 1U] == (uint8_t)'*' && false) {",
        ),
        InfoMutant(
            "M39_joint_mdl_reset_ws",
            "alpha_mdl_canon",
            "    for (uint32_t idx = 0U; idx < count; idx++) {\n"
            "        const uint8_t *cur = streams[idx];",
            "    for (uint32_t idx = 0U; idx < count; idx++) {\n"
            "        info_ws_reset(ws);\n"
            "        pred_init(&st, flags);\n"
            "        const uint8_t *cur = streams[idx];",
        ),
    ]


def _run_one_mutant(
    mutant: InfoMutant,
    ring0_src: str,
    cli_path: Path,
    repo_root: Path,
    flow_core: Path,
    flow_sdk: Path,
    cc: str,
) -> tuple[InfoMutant, int, int, int, str]:
    count = ring0_src.count(mutant.target)
    if count != 1:
        return (mutant, count, -1, -1, f"target match count={count} (expected 1)")

    mutated = ring0_src.replace(mutant.target, mutant.replacement, 1)
    with tempfile.TemporaryDirectory(prefix=f"inf_mut_{mutant.name}_") as td:
        tmp_dir = Path(td)
        mut_c = tmp_dir / "info_ring0.c"
        mut_o = tmp_dir / "info_ring0.o"
        exe_path = tmp_dir / "info_test"
        mut_c.write_text(mutated, encoding="utf-8")

        ring0_flags = [
            cc,
            "-std=c17",
            "-O2",
            "-ffreestanding",
            "-nostdlib",
            "-fno-builtin",
            "-fno-stack-protector",
            "-fno-jump-tables",
            "-mgeneral-regs-only",
            "-Wall",
            "-Wextra",
            "-Wpedantic",
            "-Wconversion",
            "-Wundef",
            "-Wmissing-prototypes",
            "-Werror",
            "-I",
            str(repo_root / "include"),
            "-I",
            str(repo_root / "build"),
            "-isystem",
            str(flow_core),
            "-isystem",
            str(flow_sdk),
            "-c",
            str(mut_c),
            "-o",
            str(mut_o),
        ]
        c1 = subprocess.run(ring0_flags, capture_output=True, text=True, check=False)
        if c1.returncode != 0:
            return (mutant, count, c1.returncode, -1, f"ring0 compile failed:\n{c1.stderr.strip()}")

        cli_flags = [
            cc,
            "-std=c17",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Wpedantic",
            "-Wconversion",
            "-Wundef",
            "-Wmissing-prototypes",
            "-Werror",
            "-I",
            str(repo_root / "include"),
            "-I",
            str(repo_root / "build"),
            "-isystem",
            str(flow_core),
            "-isystem",
            str(flow_sdk),
            str(cli_path),
            str(mut_o),
            "-o",
            str(exe_path),
        ]
        c2 = subprocess.run(cli_flags, capture_output=True, text=True, check=False)
        if c2.returncode != 0:
            return (mutant, count, c2.returncode, -1, f"cli link failed:\n{c2.stderr.strip()}")

        run = subprocess.run([str(exe_path), "selftest"], capture_output=True, text=True, check=False)
        detail = (run.stdout or run.stderr).strip()
        return (mutant, count, 0, run.returncode, detail)


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    ring0_path = repo_root / "src" / "info_ring0.c"
    cli_path = repo_root / "src" / "info_cli.c"
    schema_hdr = repo_root / "build" / "info_schema_abi.h"
    flow_dir = Path(os.environ.get("FLOW_DIR", str(repo_root.parent / "FLOW"))).resolve()
    flow_core = flow_dir / "core"
    flow_sdk = flow_dir / "sdk"
    cc = os.environ.get("CC", "clang")
    if not Path(cc).exists() and Path("/opt/homebrew/opt/llvm/bin/clang").exists():
        cc = "/opt/homebrew/opt/llvm/bin/clang"

    if not schema_hdr.is_file():
        print(f"ERROR: missing {schema_hdr}; run `make all` first.", file=sys.stderr)
        return 1

    ring0_src = ring0_path.read_text(encoding="utf-8")
    mutants = build_info_mutants()

    t0 = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="inf_mut_base_") as td:
        tmp_dir = Path(td)
        base_obj = tmp_dir / "info_ring0.o"
        base_exe = tmp_dir / "info"
        b1 = subprocess.run(
            [
                cc, "-std=c17", "-O2", "-ffreestanding", "-nostdlib", "-fno-builtin",
                "-fno-stack-protector", "-fno-jump-tables", "-mgeneral-regs-only",
                "-Wall", "-Wextra", "-Wpedantic", "-Wconversion", "-Wundef", "-Wmissing-prototypes", "-Werror",
                "-I", str(repo_root / "include"), "-I", str(repo_root / "build"),
                "-isystem", str(flow_core), "-isystem", str(flow_sdk),
                "-c", str(ring0_path), "-o", str(base_obj),
            ],
            capture_output=True, text=True, check=False,
        )
        assert b1.returncode == 0, f"Baseline ring0 compile failed:\n{b1.stderr}"
        b2 = subprocess.run(
            [
                cc, "-std=c17", "-O2", "-Wall", "-Wextra", "-Wpedantic", "-Wconversion",
                "-Wundef", "-Wmissing-prototypes", "-Werror",
                "-I", str(repo_root / "include"), "-I", str(repo_root / "build"),
                "-isystem", str(flow_core), "-isystem", str(flow_sdk),
                str(cli_path), str(base_obj), "-o", str(base_exe),
            ],
            capture_output=True, text=True, check=False,
        )
        assert b2.returncode == 0, f"Baseline CLI build failed:\n{b2.stderr}"
        br = subprocess.run([str(base_exe), "selftest"], capture_output=True, text=True, check=False)
        assert br.returncode == 0, f"Baseline selftest failed:\n{br.stdout}\n{br.stderr}"

    workers = min(8, max(1, (os.cpu_count() or 4)))
    results: list[tuple[InfoMutant, int, int, int, str]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        futs = [
            ex.submit(_run_one_mutant, m, ring0_src, cli_path, repo_root, flow_core, flow_sdk, cc)
            for m in mutants
        ]
        for f in futs:
            results.append(f.result())

    killed = 0
    bad = 0
    cat_counts: dict[str, list[int]] = {}
    for m, count, comp_rc, run_rc, detail in results:
        cat_counts.setdefault(m.category, [0, 0])
        cat_counts[m.category][1] += 1
        if count == 1 and comp_rc == 0 and run_rc != 0:
            killed += 1
            cat_counts[m.category][0] += 1
            print(f"  [KILLED] {m.category:22s} | {m.name:34s} (rc={run_rc})")
        else:
            bad += 1
            print(
                f"  [SURVIVED/ERR] {m.category:22s} | {m.name:34s} "
                f"(count={count} cc={comp_rc} rc={run_rc})\n    {detail}"
            )

    dt = time.monotonic() - t0
    pct = (100.0 * killed / len(mutants)) if mutants else 0.0
    print("  --- Category Summary ---")
    for cat, (k, tot) in cat_counts.items():
        print(f"    {cat:22s}: {k}/{tot}")
    print(f"  [SABOTAGE-GATE] killed={killed}/{len(mutants)} ({pct:.1f}%) in {dt:.2f}s")
    return 0 if (bad == 0 and killed == len(mutants)) else 1


if __name__ == "__main__":
    raise SystemExit(main())
