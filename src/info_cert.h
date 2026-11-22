#ifndef INFO_CERT_H
#define INFO_CERT_H

#include "flow_ir_builder.h"
#include "flow_ir_io.h"
#include "info.h"

#include <stdio.h>

typedef flow_ir_builder_ws_t info_cert_ws_t;

static inline uint32_t info_cert_emit_const(flow_ir_prog_t *p, uint16_t width, uint64_t val,
                                            const char *name) {
    return flow_ir_emit_const(p, width, val, name);
}

static inline uint32_t info_cert_emit_op1(flow_ir_prog_t *p, uint16_t kind, uint16_t width,
                                          uint32_t in0, uint64_t p0, const char *name) {
    return flow_ir_emit_op1(p, kind, width, in0, p0, name);
}

static inline uint32_t info_cert_emit_op2(flow_ir_prog_t *p, uint16_t kind, uint16_t width,
                                          uint32_t lhs, uint32_t rhs, const char *name) {
    return flow_ir_emit_op2(p, kind, width, lhs, rhs, name);
}

static inline uint32_t info_cert_emit_sel(flow_ir_prog_t *p, uint16_t width, uint32_t sel,
                                          uint32_t vf, uint32_t vt, const char *name) {
    return flow_ir_emit_sel(p, width, sel, vf, vt, name);
}

static inline void info_cert_init_prog(info_cert_ws_t *ws, const char *name) {
    flow_ir_builder_init(ws, name);
}

static inline bool info_cert_seal_and_write_fir(info_cert_ws_t *ws, const char *out_fir_path) {
    return flow_ir_builder_seal_and_write(ws, out_fir_path);
}

/* ============================================================================
 * 1. Hunt: `alg-blindspot` (.lean, .fir, .json)
 * ============================================================================ */

static inline bool info_cert_emit_alg_lean(const info_hunt_alg_t *w, const char *path) {
    if (w == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp, "import Info.Theory\n\n");
    fprintf(fp, "namespace Info.CertAlgBlindspot\n\n");
    fprintf(fp, "open Info.Induction\n\n");
    fprintf(fp, "def witnessInit : BitVec 16 := 0x%04x#16\n\n", (unsigned)w->init_state);
    fprintf(fp, "theorem witness_lfsr16_zero_residual :\n");
    fprintf(
        fp,
        "    (lfsr16Advance witnessInit >>> 15).truncate 1 ^^^ lfsr16NextBit witnessInit = 0#1 := by\n");
    fprintf(fp, "  exact lfsr16_step_zero_residual_bv16 witnessInit\n\n");
    fprintf(fp, "theorem witness_alg_strictly_beats_ctx :\n");
    fprintf(fp, "    (%llu : Nat) < %llu := by\n", (unsigned long long)w->full_alg_bytes,
            (unsigned long long)w->pure_ctx_bytes);
    fprintf(fp, "  omega\n\n");
    fprintf(fp, "theorem witness_stat_context_blind_on_depth3 (ctx : BitVec 3) :\n");
    fprintf(fp, "    ∃ b0 b1 : Bool, b0 ≠ b1 ∧ lfsr4Step (ctx.cons b0) = true ∧\n");
    fprintf(fp, "      lfsr4Step (ctx.cons b1) = false :=\n");
    fprintf(fp, "  depth3_lfsr4_balanced_nogo ctx\n\n");
    fprintf(fp, "end Info.CertAlgBlindspot\n");
    return fclose(fp) == 0;
}

static inline bool info_cert_emit_alg_fir(const info_hunt_alg_t *w, const char *out_fir_path,
                                          info_cert_ws_t *ws) {
    if (w == NULL || ws == NULL) {
        return false;
    }
    info_cert_init_prog(ws, "info_lfsr16_step");
    flow_ir_prog_t *p = &ws->ir_prog;
    p->num_inputs = 1U;
    p->inputs[0] = 0U;
    p->vals[0].width = 16U;
    p->vals[0].is_classical = 0U;
    (void)snprintf(p->vals[0].name, sizeof(p->vals[0].name), "state16");
    p->num_vals = 1U;

    uint32_t m1 = info_cert_emit_const(p, 16U, UINT64_C(1), "m1");
    uint32_t c1 = info_cert_emit_const(p, 16U, UINT64_C(1), "c1");
    uint32_t c2 = info_cert_emit_const(p, 16U, UINT64_C(2), "c2");
    uint32_t c3 = info_cert_emit_const(p, 16U, UINT64_C(3), "c3");
    uint32_t c5 = info_cert_emit_const(p, 16U, UINT64_C(5), "c5");
    uint32_t c15 = info_cert_emit_const(p, 16U, UINT64_C(15), "c15");
    uint32_t s1 = info_cert_emit_op2(p, FLOW_IR_OP_SHR_VAR, 16U, 0U, c1, "s1");
    uint32_t s2 = info_cert_emit_op2(p, FLOW_IR_OP_SHR_VAR, 16U, 0U, c2, "s2");
    uint32_t s3 = info_cert_emit_op2(p, FLOW_IR_OP_SHR_VAR, 16U, 0U, c3, "s3");
    uint32_t s5 = info_cert_emit_op2(p, FLOW_IR_OP_SHR_VAR, 16U, 0U, c5, "s5");
    uint32_t x02 = info_cert_emit_op2(p, FLOW_IR_OP_XOR_VEC, 16U, 0U, s2, "x02");
    uint32_t x35 = info_cert_emit_op2(p, FLOW_IR_OP_XOR_VEC, 16U, s3, s5, "x35");
    uint32_t xall = info_cert_emit_op2(p, FLOW_IR_OP_XOR_VEC, 16U, x02, x35, "xall");
    uint32_t nbit = info_cert_emit_op2(p, FLOW_IR_OP_AND_VEC, 16U, xall, m1, "nbit");
    uint32_t top = info_cert_emit_op2(p, FLOW_IR_OP_SHL_VAR, 16U, nbit, c15, "top");
    uint32_t out_s = info_cert_emit_op2(p, FLOW_IR_OP_XOR_VEC, 16U, s1, top, "next16");
    if (out_s == UINT32_MAX) {
        return false;
    }
    p->num_outputs = 1U;
    p->outputs[0] = out_s;
    if (!info_cert_seal_and_write_fir(ws, out_fir_path)) {
        return false;
    }
    bool match = true;
    for (uint32_t i = 0U; i < 16U; i++) {
        uint32_t s = ((uint32_t)w->init_state + i * UINT32_C(0x1111)) & UINT32_C(0xFFFF);
        uint32_t nxt = ((s >> 0U) ^ (s >> 2U) ^ (s >> 3U) ^ (s >> 5U)) & UINT32_C(1);
        uint32_t exp_s = (s >> 1U) | (nxt << 15U);
        uint64_t inv[1] = {(uint64_t)s};
        uint64_t outv[1] = {UINT64_C(0)};
        if (!flow_ir_eval_u64(&ws->ir_reloaded, inv, outv) ||
            (outv[0] & UINT64_C(0xFFFF)) != (uint64_t)exp_s) {
            match = false;
            break;
        }
    }
    ws->ir_eval_ok = match;
    return match;
}

static inline bool info_cert_emit_alg_json(const info_hunt_alg_t *w, const info_cert_ws_t *ws,
                                           const char *path) {
    if (w == NULL || ws == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp,
            "{\n"
            "  \"mode\": \"alg-blindspot\",\n"
            "  \"seed\": \"0x%016llx\",\n"
            "  \"stream_bytes\": %llu,\n"
            "  \"pure_ctx_bytes\": %llu,\n"
            "  \"full_alg_bytes\": %llu,\n"
            "  \"alg_hits\": %llu,\n"
            "  \"init_state\": \"0x%04x\",\n"
            "  \"roundtrip_ok\": %u,\n"
            "  \"merkle\": \"0x%016llx\",\n"
            "  \"fir_wire_bytes\": %zu,\n"
            "  \"fir_eval_ok\": %s\n"
            "}\n",
            (unsigned long long)w->seed, (unsigned long long)w->stream_bytes,
            (unsigned long long)w->pure_ctx_bytes, (unsigned long long)w->full_alg_bytes,
            (unsigned long long)w->alg_hits, (unsigned)w->init_state, (unsigned)w->roundtrip_ok,
            (unsigned long long)w->merkle, ws->wire_len, ws->ir_eval_ok ? "true" : "false");
    return fclose(fp) == 0;
}

/* ============================================================================
 * 2. Hunt: `ctw-switch` (.lean, .fir, .json)
 * ============================================================================ */

static inline bool info_cert_emit_ctw_lean(const info_hunt_ctw_t *w, const char *path) {
    if (w == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp, "import Info.Theory\n\n");
    fprintf(fp, "namespace Info.CertCtwSwitch\n\n");
    fprintf(fp, "open Info.Coding Info.Induction\n\n");
    fprintf(fp, "theorem witness_sw_ctw_dominates_static :\n");
    fprintf(fp, "    (%llu : Nat) < %llu := by\n", (unsigned long long)w->sw_bits_q12,
            (unsigned long long)w->ctw_bits_q12);
    fprintf(fp, "  omega\n\n");
    fprintf(fp, "theorem witness_kt_conservation (a b : Nat) :\n");
    fprintf(fp, "    (2 * a + 1) + (2 * b + 1) = 2 * (a + b + 1) :=\n");
    fprintf(fp, "  kt_step_conservation a b\n\n");
    fprintf(fp, "theorem witness_mixture_regret_bound (wSw pSw pRest : Nat) :\n");
    fprintf(fp, "    wSw * pSw ≤ wSw * pSw + pRest :=\n");
    fprintf(fp, "  switching_segment_regret_bound wSw pSw pRest\n\n");
    fprintf(fp, "end Info.CertCtwSwitch\n");
    return fclose(fp) == 0;
}

static inline bool info_cert_emit_ctw_fir(const info_hunt_ctw_t *w, const char *out_fir_path,
                                          info_cert_ws_t *ws) {
    if (w == NULL || ws == NULL) {
        return false;
    }
    info_cert_init_prog(ws, "info_ctw_switch_sel");
    flow_ir_prog_t *p = &ws->ir_prog;
    p->num_inputs = 3U;
    p->inputs[0] = 0U;
    p->inputs[1] = 1U;
    p->inputs[2] = 2U;
    p->vals[0].width = 1U;
    p->vals[1].width = 8U;
    p->vals[2].width = 8U;
    (void)snprintf(p->vals[0].name, sizeof(p->vals[0].name), "sw_flag");
    (void)snprintf(p->vals[1].name, sizeof(p->vals[1].name), "regime0_p");
    (void)snprintf(p->vals[2].name, sizeof(p->vals[2].name), "regime1_p");
    p->num_vals = 3U;

    uint32_t chosen = info_cert_emit_sel(p, 8U, 0U, 1U, 2U, "p_active");
    if (chosen == UINT32_MAX) {
        return false;
    }
    p->num_outputs = 1U;
    p->outputs[0] = chosen;
    if (!info_cert_seal_and_write_fir(ws, out_fir_path)) {
        return false;
    }
    bool match = true;
    for (uint32_t sw = 0U; sw < 2U; sw++) {
        for (uint32_t v = 0U; v < 4U; v++) {
            uint64_t r0 = UINT64_C(224) - (uint64_t)v * UINT64_C(16);
            uint64_t r1 = UINT64_C(32) + (uint64_t)v * UINT64_C(16);
            uint64_t inv[3] = {(uint64_t)sw, r0, r1};
            uint64_t outv[1] = {UINT64_C(0)};
            uint64_t exp_v = (sw != 0U) ? r1 : r0;
            if (!flow_ir_eval_u64(&ws->ir_reloaded, inv, outv) ||
                (outv[0] & UINT64_C(0xFF)) != exp_v) {
                match = false;
                break;
            }
        }
    }
    ws->ir_eval_ok = match;
    return match;
}

static inline bool info_cert_emit_ctw_json(const info_hunt_ctw_t *w, const info_cert_ws_t *ws,
                                           const char *path) {
    if (w == NULL || ws == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp,
            "{\n"
            "  \"mode\": \"ctw-switch\",\n"
            "  \"seed\": \"0x%016llx\",\n"
            "  \"len\": %llu,\n"
            "  \"switch_pos\": %llu,\n"
            "  \"ctw_bits_q12\": %llu,\n"
            "  \"sw_bits_q12\": %llu,\n"
            "  \"reg_diff_q12\": %llu,\n"
            "  \"sw_dominates\": %u,\n"
            "  \"merkle\": \"0x%016llx\",\n"
            "  \"fir_wire_bytes\": %zu,\n"
            "  \"fir_eval_ok\": %s\n"
            "}\n",
            (unsigned long long)w->seed, (unsigned long long)w->len,
            (unsigned long long)w->switch_pos, (unsigned long long)w->ctw_bits_q12,
            (unsigned long long)w->sw_bits_q12, (unsigned long long)w->reg_diff_q12,
            (unsigned)w->sw_dominates, (unsigned long long)w->merkle, ws->wire_len,
            ws->ir_eval_ok ? "true" : "false");
    return fclose(fp) == 0;
}

/* ============================================================================
 * 3. Hunt: `delsarte-gap` (.lean, .fir, .json)
 * ============================================================================ */

static inline bool info_cert_emit_delsarte_lean(const info_hunt_delsarte_t *w, const char *path) {
    if (w == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    uint32_t dim = w->n + 1U;
    fprintf(fp, "import Info.Theory\n\n");
    fprintf(fp, "namespace Info.CertDelsarteGap\n\n");
    fprintf(fp, "open Info.Bounds\n\n");
    fprintf(fp, "def yDual : Fin %u → Int\n", (unsigned)dim);
    for (uint32_t k = 0U; k < dim; k++) {
        fprintf(fp, "  | %u => %lld\n", (unsigned)k, (long long)w->dual_y[k]);
    }
    fprintf(fp, "\ndef kMat : Fin %u → Fin %u → Int\n", (unsigned)dim, (unsigned)dim);
    fprintf(fp, "  | k, j => \n");
    for (uint32_t k = 0U; k < dim; k++) {
        for (uint32_t j = 0U; j < dim; j++) {
            int64_t kv = info_krawtchouk_int(w->n, k, j);
            if (k == 0U && j == 0U) {
                fprintf(fp, "    if k.val = 0 ∧ j.val = 0 then %lld\n", (long long)kv);
            } else {
                fprintf(fp, "    else if k.val = %u ∧ j.val = %u then %lld\n", (unsigned)k,
                        (unsigned)j, (long long)kv);
            }
        }
    }
    fprintf(fp, "    else 0\n\n");
    fprintf(fp, "theorem witness_dual_y_nonneg (k : Fin %u) : 0 ≤ yDual k := by\n", (unsigned)dim);
    fprintf(fp, "  revert k; decide\n\n");
    fprintf(fp, "theorem witness_delsarte_tail_nonpos (j : Fin %u) (hj : %u ≤ j.val) :\n",
            (unsigned)dim, (unsigned)w->d);
    fprintf(
        fp,
        "    yDual 0 + sumFin %u (fun k => if k.val = 0 then 0 else yDual k * kMat k j) ≤ 0 := by\n",
        (unsigned)dim);
    fprintf(fp, "  revert j hj; decide\n\n");
    fprintf(fp, "theorem witness_searu_within_delsarte_ub :\n");
    fprintf(fp, "    (%llu : Nat) * %llu ≤ %llu := by\n", (unsigned long long)w->searu_size,
            (unsigned long long)w->delsarte_den, (unsigned long long)w->delsarte_num);
    fprintf(fp, "  omega\n\n");
    fprintf(fp, "end Info.CertDelsarteGap\n");
    return fclose(fp) == 0;
}

static inline bool info_cert_emit_delsarte_fir(const info_hunt_delsarte_t *w,
                                               const char *out_fir_path, info_cert_ws_t *ws) {
    if (w == NULL || ws == NULL) {
        return false;
    }
    info_cert_init_prog(ws, "info_code_xor_dist");
    flow_ir_prog_t *p = &ws->ir_prog;
    p->num_inputs = 2U;
    p->inputs[0] = 0U;
    p->inputs[1] = 1U;
    p->vals[0].width = 7U;
    p->vals[1].width = 7U;
    (void)snprintf(p->vals[0].name, sizeof(p->vals[0].name), "cw_a");
    (void)snprintf(p->vals[1].name, sizeof(p->vals[1].name), "cw_b");
    p->num_vals = 2U;

    uint32_t diff = info_cert_emit_op2(p, FLOW_IR_OP_XOR_VEC, 7U, 0U, 1U, "syndrome");
    if (diff == UINT32_MAX) {
        return false;
    }
    p->num_outputs = 1U;
    p->outputs[0] = diff;
    if (!info_cert_seal_and_write_fir(ws, out_fir_path)) {
        return false;
    }
    bool match = true;
    uint32_t limit = (w->searu_size < 16U) ? (uint32_t)w->searu_size : 16U;
    for (uint32_t i = 0U; i < limit; i++) {
        uint32_t j = (i + 1U < limit) ? (i + 1U) : 0U;
        uint64_t inv[2] = {(uint64_t)w->codewords[i], (uint64_t)w->codewords[j]};
        uint64_t outv[1] = {UINT64_C(0)};
        uint64_t exp_d = (uint64_t)(w->codewords[i] ^ w->codewords[j]);
        if (!flow_ir_eval_u64(&ws->ir_reloaded, inv, outv) || (outv[0] & 0x7FU) != exp_d) {
            match = false;
            break;
        }
    }
    ws->ir_eval_ok = match;
    return match;
}

static inline bool info_cert_emit_delsarte_json(const info_hunt_delsarte_t *w,
                                                const info_cert_ws_t *ws, const char *path) {
    if (w == NULL || ws == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp,
            "{\n"
            "  \"mode\": \"delsarte-gap\",\n"
            "  \"seed\": \"0x%016llx\",\n"
            "  \"n\": %u,\n"
            "  \"d\": %u,\n"
            "  \"searu_size\": %llu,\n"
            "  \"delsarte_num\": %llu,\n"
            "  \"delsarte_den\": %llu,\n"
            "  \"hamming_ub\": %llu,\n"
            "  \"dual_ok\": %u,\n"
            "  \"merkle\": \"0x%016llx\",\n"
            "  \"fir_wire_bytes\": %zu,\n"
            "  \"fir_eval_ok\": %s\n"
            "}\n",
            (unsigned long long)w->seed, (unsigned)w->n, (unsigned)w->d,
            (unsigned long long)w->searu_size, (unsigned long long)w->delsarte_num,
            (unsigned long long)w->delsarte_den, (unsigned long long)w->hamming_ub,
            (unsigned)w->dual_ok, (unsigned long long)w->merkle, ws->wire_len,
            ws->ir_eval_ok ? "true" : "false");
    return fclose(fp) == 0;
}

/* ============================================================================
 * 4. Hunt: `balke-pearl` (.lean, .fir, .json)
 * ============================================================================ */

static inline bool info_cert_emit_bp_lean(const info_hunt_bp_t *w, const char *path) {
    if (w == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp, "import Info.Theory\n\n");
    fprintf(fp, "namespace Info.CertBalkePearl\n\n");
    fprintf(fp, "open Info.Causal\n\n");
    fprintf(fp, "theorem witness_bp_interval_valid :\n");
    fprintf(fp, "    (%lld : Int) ≤ %lld ∧ (%lld : Int) ≤ %lld := by\n", (long long)w->low_num,
            (long long)w->true_num, (long long)w->true_num, (long long)w->high_num);
    fprintf(fp, "  omega\n\n");
    fprintf(fp, "theorem witness_obs_equiv_nogo :\n");
    fprintf(
        fp,
        "    (∀ x y : Bool, jointFwd x y = jointRev x y) ∧ doXTrueProbY true ≠ doXTrueProbY false :=\n");
    fprintf(fp, "  causal_obs_equiv_nogo\n\n");
    fprintf(fp, "theorem witness_natural_envelope (s : IVStrata) :\n");
    fprintf(fp, "    -((s.total : Int)) ≤ s.aceNum ∧ s.aceNum ≤ (s.total : Int) :=\n");
    fprintf(fp, "  balke_pearl_natural_bounds s\n\n");
    fprintf(fp, "end Info.CertBalkePearl\n");
    return fclose(fp) == 0;
}

static inline bool info_cert_emit_bp_fir(const info_hunt_bp_t *w, const char *out_fir_path,
                                         info_cert_ws_t *ws) {
    if (w == NULL || ws == NULL) {
        return false;
    }
    info_cert_init_prog(ws, "info_bp_natural_mux");
    flow_ir_prog_t *p = &ws->ir_prog;
    p->num_inputs = 3U;
    p->inputs[0] = 0U;
    p->inputs[1] = 1U;
    p->inputs[2] = 2U;
    p->vals[0].width = 1U;
    p->vals[1].width = 16U;
    p->vals[2].width = 16U;
    (void)snprintf(p->vals[0].name, sizeof(p->vals[0].name), "bound_sel");
    (void)snprintf(p->vals[1].name, sizeof(p->vals[1].name), "bp_lo_u16");
    (void)snprintf(p->vals[2].name, sizeof(p->vals[2].name), "bp_hi_u16");
    p->num_vals = 3U;

    uint32_t out_b = info_cert_emit_sel(p, 16U, 0U, 1U, 2U, "bp_bound");
    if (out_b == UINT32_MAX) {
        return false;
    }
    p->num_outputs = 1U;
    p->outputs[0] = out_b;
    if (!info_cert_seal_and_write_fir(ws, out_fir_path)) {
        return false;
    }
    bool match = true;
    uint32_t lo16 = (uint32_t)((int32_t)w->low_num + 256);
    uint32_t hi16 = (uint32_t)((int32_t)w->high_num + 256);
    for (uint32_t sel = 0U; sel < 2U; sel++) {
        uint64_t inv[3] = {(uint64_t)sel, (uint64_t)lo16, (uint64_t)hi16};
        uint64_t outv[1] = {UINT64_C(0)};
        uint64_t exp_b = (sel != 0U) ? (uint64_t)hi16 : (uint64_t)lo16;
        if (!flow_ir_eval_u64(&ws->ir_reloaded, inv, outv) || (outv[0] & 0xFFFFU) != exp_b) {
            match = false;
            break;
        }
    }
    ws->ir_eval_ok = match;
    return match;
}

static inline bool info_cert_emit_bp_json(const info_hunt_bp_t *w, const info_cert_ws_t *ws,
                                          const char *path) {
    if (w == NULL || ws == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp,
            "{\n"
            "  \"mode\": \"balke-pearl\",\n"
            "  \"seed\": \"0x%016llx\",\n"
            "  \"low_num\": %lld,\n"
            "  \"high_num\": %lld,\n"
            "  \"den\": %llu,\n"
            "  \"true_num\": %lld,\n"
            "  \"natural_bound_ok\": %u,\n"
            "  \"obs_equiv_ok\": %u,\n"
            "  \"merkle\": \"0x%016llx\",\n"
            "  \"fir_wire_bytes\": %zu,\n"
            "  \"fir_eval_ok\": %s\n"
            "}\n",
            (unsigned long long)w->seed, (long long)w->low_num, (long long)w->high_num,
            (unsigned long long)w->den, (long long)w->true_num, (unsigned)w->natural_bound_ok,
            (unsigned)w->obs_equiv_ok, (unsigned long long)w->merkle, ws->wire_len,
            ws->ir_eval_ok ? "true" : "false");
    return fclose(fp) == 0;
}

/* ============================================================================
 * 5. Hunt: `causal-mdl` (.lean, .fir, .json)
 * ============================================================================ */

static inline bool info_cert_emit_causal_mdl_lean(const info_hunt_causal_mdl_t *w,
                                                  const char *path) {
    if (w == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp, "import Info.Theory\n\n");
    fprintf(fp, "namespace Info.CertCausalMdl\n\n");
    fprintf(fp, "open Info.Causal\n\n");
    fprintf(fp, "theorem witness_causal_direction_shorter :\n");
    fprintf(fp, "    (%llu : Nat) < %llu := by\n", (unsigned long long)w->lxy_total_q12,
            (unsigned long long)w->lyx_total_q12);
    fprintf(fp, "  omega\n\n");
    fprintf(fp, "theorem witness_interventional_mdl_separation\n");
    fprintf(fp, "    (lx1 lx2 lyx ly1 ly2 lxy1 lxy2 d1 d2 : Nat)\n");
    fprintf(fp, "    (hM : lx1 + lx2 ≤ ly1 + ly2) (hS : lyx < lxy1 + lxy2) :\n");
    fprintf(fp, "    lx1 + lx2 + lyx + d1 + d2 < ly1 + ly2 + lxy1 + lxy2 + d1 + d2 :=\n");
    fprintf(fp,
            "  causal_mdl_true_direction_shorter lx1 lx2 lyx ly1 ly2 lxy1 lxy2 d1 d2 hM hS\n\n");
    fprintf(fp, "end Info.CertCausalMdl\n");
    return fclose(fp) == 0;
}

static inline bool info_cert_emit_causal_mdl_fir(const info_hunt_causal_mdl_t *w,
                                                 const char *out_fir_path, info_cert_ws_t *ws) {
    if (w == NULL || ws == NULL) {
        return false;
    }
    info_cert_init_prog(ws, "info_causal_mdl_cmp");
    flow_ir_prog_t *p = &ws->ir_prog;
    p->num_inputs = 2U;
    p->inputs[0] = 0U;
    p->inputs[1] = 1U;
    p->vals[0].width = 32U;
    p->vals[1].width = 32U;
    (void)snprintf(p->vals[0].name, sizeof(p->vals[0].name), "l_xy_q12");
    (void)snprintf(p->vals[1].name, sizeof(p->vals[1].name), "l_yx_q12");
    p->num_vals = 2U;

    uint32_t sh32 = info_cert_emit_const(p, 8U, UINT64_C(32), "sh32");
    uint32_t diff33 = info_cert_emit_op2(p, FLOW_IR_OP_SUB, 33U, 0U, 1U, "diff33");
    uint32_t d = info_cert_emit_op2(p, FLOW_IR_OP_SHR_VAR, 1U, diff33, sh32, "dir_x_to_y");
    if (d == UINT32_MAX) {
        return false;
    }
    p->num_outputs = 1U;
    p->outputs[0] = d;
    if (!info_cert_seal_and_write_fir(ws, out_fir_path)) {
        return false;
    }
    uint64_t inv[2] = {w->lxy_total_q12 & UINT64_C(0xFFFFFFFF),
                       w->lyx_total_q12 & UINT64_C(0xFFFFFFFF)};
    uint64_t outv[1] = {UINT64_C(0)};
    bool match = flow_ir_eval_u64(&ws->ir_reloaded, inv, outv) &&
                 ((outv[0] & 1U) == (w->lxy_total_q12 < w->lyx_total_q12 ? UINT64_C(1) : 0U));
    ws->ir_eval_ok = match;
    return match;
}

static inline bool info_cert_emit_causal_mdl_json(const info_hunt_causal_mdl_t *w,
                                                  const info_cert_ws_t *ws, const char *path) {
    if (w == NULL || ws == NULL || path == NULL) {
        return false;
    }
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    fprintf(fp,
            "{\n"
            "  \"mode\": \"causal-mdl\",\n"
            "  \"seed\": \"0x%016llx\",\n"
            "  \"stream_bytes\": %llu,\n"
            "  \"lx_bits_q12\": %llu,\n"
            "  \"ly_bits_q12\": %llu,\n"
            "  \"ly_given_x_bits_q12\": %llu,\n"
            "  \"lx_given_y_bits_q12\": %llu,\n"
            "  \"lxy_total_q12\": %llu,\n"
            "  \"lyx_total_q12\": %llu,\n"
            "  \"dir_recovered\": %u,\n"
            "  \"merkle\": \"0x%016llx\",\n"
            "  \"fir_wire_bytes\": %zu,\n"
            "  \"fir_eval_ok\": %s\n"
            "}\n",
            (unsigned long long)w->seed, (unsigned long long)w->stream_bytes,
            (unsigned long long)w->lx_bits_q12, (unsigned long long)w->ly_bits_q12,
            (unsigned long long)w->ly_given_x_bits_q12, (unsigned long long)w->lx_given_y_bits_q12,
            (unsigned long long)w->lxy_total_q12, (unsigned long long)w->lyx_total_q12,
            (unsigned)w->dir_recovered, (unsigned long long)w->merkle, ws->wire_len,
            ws->ir_eval_ok ? "true" : "false");
    return fclose(fp) == 0;
}

#endif /* INFO_CERT_H */
