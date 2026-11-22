#!/usr/bin/env python3
"""
tools/info_sabotage_check.py — 42-Mutant Single-Fault Sabotage Gate (Gate 6)
===============================================================================
Verifies 100.0% mutation-kill efficacy (42/42 killed, 0 compile errors) across
14 categories (3 mutants each) in `src/info_ring0.c`:
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
  13. alpha_mdl_canon      (3)
  14. lean_expr_canon      (3)
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

FLOW_TOOLS_DIR = (
    Path(os.environ.get("FLOW_DIR", str(Path(__file__).resolve().parents[2] / "FLOW"))).resolve()
    / "sdk"
    / "tools"
)
if str(FLOW_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(FLOW_TOOLS_DIR))

from flow_sabotage_runner import FlowMutant, run_sabotage_suite

InfoMutant = FlowMutant


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
        # --- 14. lean_expr_canon (3) ---
        InfoMutant(
            "M40_expr_disable_op_preserve",
            "lean_expr_canon",
            "    if (lang == INFO_LANG_LEAN_EXPR) {\n"
            "        for (size_t i = 0U; i < sizeof(k_kw_expr) / sizeof(k_kw_expr[0]); i++) {\n"
            "            if (alpha_tok_eq(tok, len, k_kw_expr[i])) {\n"
            "                return true;\n"
            "            }\n"
            "        }",
            "    if (lang == INFO_LANG_LEAN_EXPR) {\n"
            "        for (size_t i = 0U; i < sizeof(k_kw_expr) / sizeof(k_kw_expr[0]); i++) {\n"
            "            if (false && alpha_tok_eq(tok, len, k_kw_expr[i])) {\n"
            "                return true;\n"
            "            }\n"
            "        }",
        ),
        InfoMutant(
            "M41_expr_disable_dot_atom",
            "lean_expr_canon",
            "    return lang == INFO_LANG_LEAN_EXPR && (ch == (uint8_t)'.' || ch == (uint8_t)'\\'');",
            "    return lang == INFO_LANG_LEAN_EXPR && ch == (uint8_t)'\\'';",
        ),
        InfoMutant(
            "M42_expr_preserve_all_consts",
            "lean_expr_canon",
            "        return alpha_is_indexed_op(tok, len, \"BV\") || alpha_is_indexed_op(tok, len, \"REF\") ||\n"
            "               alpha_is_indexed_op(tok, len, \"LV\");\n"
            "    }",
            "        (void)alpha_is_indexed_op(tok, len, \"BV\");\n"
            "        return true;\n"
            "    }",
        ),
    ]


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    return run_sabotage_suite(
        ring0_path=repo_root / "src" / "info_ring0.c",
        cli_path=repo_root / "src" / "info_cli.c",
        schema_hdr=repo_root / "build" / "info_schema_abi.h",
        mutants=build_info_mutants(),
        repo_root=repo_root,
        prefix="inf_mut_",
    )


if __name__ == "__main__":
    raise SystemExit(main())
