#include "info_cert.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define INFO_CLI_MAX_BYTES (4U * 1024U * 1024U)

static info_codec_ws_t g_ws;
static info_cert_ws_t g_cert_ws;
static info_alpha_ws_t g_alpha_ws;
static uint8_t g_buf_a[INFO_CLI_MAX_BYTES + 1024U];
static uint8_t g_buf_b[INFO_CLI_MAX_BYTES + 1024U];
static uint8_t g_buf_c[INFO_CLI_MAX_BYTES + 1024U];

static bool info_cstr_eq(const char *a, const char *b) {
    if (a == NULL || b == NULL) {
        return false;
    }
    return strcmp(a, b) == 0;
}

static bool info_parse_u64(const char *s, uint64_t *out) {
    if (s == NULL || *s == '\0' || out == NULL) {
        return false;
    }
    char *endp = NULL;
    unsigned long long v = strtoull(s, &endp, 0);
    if (endp == NULL || *endp != '\0') {
        return false;
    }
    *out = (uint64_t)v;
    return true;
}

static const char *info_parse_opt(int argc, char **argv, int start, const char *flag) {
    for (int i = start; i + 1 < argc; i++) {
        if (info_cstr_eq(argv[i], flag)) {
            return argv[i + 1];
        }
    }
    return NULL;
}

static bool info_has_flag(int argc, char **argv, int start, const char *flag) {
    for (int i = start; i < argc; i++) {
        if (info_cstr_eq(argv[i], flag)) {
            return true;
        }
    }
    return false;
}

static bool info_read_file(const char *path, uint8_t *dst, size_t cap, size_t *out_len) {
    FILE *fp = fopen(path, "rb");
    if (fp == NULL) {
        return false;
    }
    size_t n = fread(dst, 1U, cap, fp);
    int extra = fgetc(fp);
    (void)fclose(fp);
    if (extra != EOF) {
        return false;
    }
    *out_len = n;
    return true;
}

static bool info_write_file(const char *path, const uint8_t *src, size_t len) {
    FILE *fp = fopen(path, "wb");
    if (fp == NULL) {
        return false;
    }
    size_t wr = (len > 0U) ? fwrite(src, 1U, len, fp) : 0U;
    int cls = fclose(fp);
    return (wr == len) && (cls == 0);
}

static bool info_mem_eq(const uint8_t *a, const uint8_t *b, size_t n) {
    for (size_t i = 0U; i < n; i++) {
        if (a[i] != b[i]) {
            return false;
        }
    }
    return true;
}

/* ============================================================================
 * T1..T16 Selftests (Zero Heap, Zero Fails)
 * ============================================================================ */

static uint32_t test_t1_t4_primitives(void) {
    uint32_t fails = UINT32_C(0);
    /* T1: E1/E2/E3 AC bit-exact roundtrip across edge lengths */
    static const size_t lens[6] = {0U, 1U, 2U, 3U, 257U, 4096U};
    for (size_t li = 0U; li < 6U; li++) {
        size_t n = lens[li];
        for (size_t i = 0U; i < n; i++) {
            g_buf_a[i] = (uint8_t)(((i * 73U + 19U) ^ (i >> 3U)) & UINT32_C(0xFF));
        }
        size_t cl = info_ac_test_roundtrip(g_buf_a, n, g_buf_b, sizeof(g_buf_b), g_buf_c);
        if (cl == 0U || (n > 0U && !info_mem_eq(g_buf_a, g_buf_c, n))) {
            fails++;
        }
    }
    /* T2: stretch / squash monotonicity & inverse agreement */
    int32_t prev_s = info_stretch(1U);
    for (uint32_t p = 16U; p <= 4095U; p += 17U) {
        int32_t st = info_stretch(p);
        if (st < prev_s) {
            fails++;
        }
        prev_s = st;
        if (p >= 64U && p <= 4032U) {
            uint32_t back = info_squash(st);
            int32_t diff = (int32_t)back - (int32_t)p;
            if (diff < -16 || diff > 16) {
                fails++;
            }
        }
    }
    /* T3: Q12 -log2 LUT exact values & monotonicity */
    uint32_t nlog_half = info_neg_log2_q12(2048U);
    uint32_t nlog_qtr = info_neg_log2_q12(1024U);
    if (nlog_half != 4096U || nlog_qtr != 8192U ||
        info_neg_log2_q12(1U) <= info_neg_log2_q12(2048U) ||
        info_neg_log2_q12(2048U) <= info_neg_log2_q12(4095U) ||
        info_neg_log2_q12(1032U) >= nlog_qtr) {
        fails++;
    }
    /* T4: INF1 short edge cases (0, 1, 2, 3, 19 bytes) + corruption rejection */
    static const size_t short_lens[5] = {0U, 1U, 2U, 3U, 19U};
    for (size_t li = 0U; li < 5U; li++) {
        size_t n = short_lens[li];
        for (size_t i = 0U; i < n; i++) {
            g_buf_a[i] = (uint8_t)('A' + (uint8_t)(i & 15U));
        }
        size_t cl = info_compress(&g_ws, g_buf_a, n, g_buf_b, sizeof(g_buf_b), INFO_CODEC_FLAG_ALG);
        size_t dl = info_decompress(&g_ws, g_buf_b, cl, g_buf_c, sizeof(g_buf_c));
        if (cl < INFO_INF1_HEADER_BYTES || dl != n ||
            (n > 0U && !info_mem_eq(g_buf_a, g_buf_c, n))) {
            fails++;
        }
        if (n > 0U) {
            g_buf_b[12] ^= UINT8_C(1); /* corrupt fnv32 */
            if (info_decompress(&g_ws, g_buf_b, cl, g_buf_c, sizeof(g_buf_c)) != SIZE_MAX) {
                fails++;
            }
        }
    }
    return fails;
}

static uint32_t test_t5_t7_codec_roundtrip(void) {
    uint32_t fails = UINT32_C(0);
    /* T5: Repetitive structured English/Code block compresses dramatically (< 1.5 bpb) & roundtrips
     */
    static const char k_sample[] =
        "theorem info_hutter_compress (x : BitVec 32) : info_decompress (info_compress x) = x := by\n"
        "  have h := arith_decode_recovers_bit_bv32 0#32 0xFFFFFFFF#32 2048#32 x\n"
        "  exact h\n";
    size_t slen = strlen(k_sample);
    size_t n = 0U;
    for (uint32_t rep = 0U; rep < 32U; rep++) {
        memcpy(g_buf_a + n, k_sample, slen);
        n += slen;
    }
    size_t cl = info_compress(&g_ws, g_buf_a, n, g_buf_b, sizeof(g_buf_b), INFO_CODEC_FLAG_ALG);
    size_t dl = info_decompress(&g_ws, g_buf_b, cl, g_buf_c, sizeof(g_buf_c));
    if (cl == 0U || cl * 8U >= n * 2U || dl != n || !info_mem_eq(g_buf_a, g_buf_c, n)) {
        fails++;
    }
    /* T5b: Order-0/1 bit-plane compression check (3 zero top bits + 5 random low bits) */
    uint64_t xr0 = UINT64_C(0xA1B2C3D4E5F60718);
    for (size_t i = 0U; i < 1024U; i++) {
        xr0 ^= (xr0 << 13U);
        xr0 ^= (xr0 >> 7U);
        xr0 ^= (xr0 << 17U);
        g_buf_c[i] = (uint8_t)(xr0 & UINT64_C(0x1F));
    }
    size_t cl_ord0 = info_compress(&g_ws, g_buf_c, 1024U, g_buf_b, sizeof(g_buf_b), UINT32_C(0));
    if (cl_ord0 == 0U || cl_ord0 > 704U) {
        fails++;
    }
    /* T5c: High-order tagged context lookup/update check: [u, v, w(u,v), r] tuples */
    uint64_t xr2 = UINT64_C(0x1122334455667788);
    for (size_t i = 0U; i < 2048U; i++) {
        xr2 ^= (xr2 << 13U);
        xr2 ^= (xr2 >> 7U);
        xr2 ^= (xr2 << 17U);
        uint32_t u = (uint32_t)(xr2 & 7U);
        uint32_t v = (uint32_t)((xr2 >> 3U) & 7U);
        uint32_t w = ((u * 37U + 11U) ^ (v * 73U + 5U) ^ ((u & v) * 19U)) & 255U;
        uint32_t r = (uint32_t)((xr2 >> 8U) & 255U);
        g_buf_c[i * 4U + 0U] = (uint8_t)u;
        g_buf_c[i * 4U + 1U] = (uint8_t)v;
        g_buf_c[i * 4U + 2U] = (uint8_t)w;
        g_buf_c[i * 4U + 3U] = (uint8_t)r;
    }
    info_stream_eval_t ev_ord2;
    info_eval_stream_bits(&g_ws, g_buf_c, 4096U, g_buf_c + 4096U, 4096U, UINT32_C(0), &ev_ord2);
    if ((ev_ord2.total_bits_q12 >> 12U) > 17400U) {
        fails++;
    }
    /* T5d: Match model hit & mismatch-cancel verification */
    uint64_t xrm = UINT64_C(0xCAFEBABEDEADBEEF);
    for (size_t i = 0U; i < 512U; i++) {
        xrm ^= (xrm << 13U);
        xrm ^= (xrm >> 7U);
        xrm ^= (xrm << 17U);
        g_buf_c[i] = (uint8_t)(xrm & 255U);
        g_buf_c[512U + i] = g_buf_c[i];
    }
    info_stream_eval_t ev_match;
    info_eval_stream_bits(&g_ws, NULL, 0U, g_buf_c, 1024U, UINT32_C(0), &ev_match);
    if (ev_match.match_hits < 3500U || ev_match.f1_bits_q12 * 16U >= ev_match.f0_bits_q12) {
        fails++;
    }
    for (size_t i = 0U; i < 256U; i++) {
        xrm ^= (xrm << 13U);
        xrm ^= (xrm >> 7U);
        xrm ^= (xrm << 17U);
        g_buf_c[i] = (uint8_t)(xrm & 255U);
        g_buf_c[256U + i] = (i < 128U) ? g_buf_c[i] : (uint8_t)(g_buf_c[i] ^ 0xFFU);
    }
    info_stream_eval_t ev_mism;
    info_eval_stream_bits(&g_ws, g_buf_c, 256U, g_buf_c + 256U, 256U, UINT32_C(0), &ev_mism);
    if ((ev_mism.f1_bits_q12 >> 12U) > 1600U) {
        fails++;
    }
    /* T6: Pseudo-random bytes must reject magic tamper & still roundtrip losslessly */
    uint64_t x = UINT64_C(0x9E3779B97F4A7C15);
    for (size_t i = 0U; i < 2048U; i++) {
        x ^= (x << 13U);
        x ^= (x >> 7U);
        x ^= (x << 17U);
        g_buf_a[i] = (uint8_t)(x & UINT64_C(0xFF));
    }
    cl = info_compress(&g_ws, g_buf_a, 2048U, g_buf_b, sizeof(g_buf_b), INFO_CODEC_FLAG_ALG);
    dl = info_decompress(&g_ws, g_buf_b, cl, g_buf_c, sizeof(g_buf_c));
    if (dl != 2048U || !info_mem_eq(g_buf_a, g_buf_c, 2048U)) {
        fails++;
    }
    g_buf_b[0] ^= UINT8_C(1);
    if (info_decompress(&g_ws, g_buf_b, cl, g_buf_c, sizeof(g_buf_c)) != SIZE_MAX) {
        fails++;
    }
    /* T7: Prefix conditional compression strictly shorter on matched domain than mismatched domain
     */
    info_stream_eval_t ev_same, ev_diff;
    size_t pfx_len = slen * 12U;
    for (size_t i = 0U; i < pfx_len; i++) {
        g_buf_c[i] = (uint8_t)((i * 199U) & UINT32_C(0xFF));
    }
    info_eval_stream_bits(&g_ws, g_buf_a, pfx_len, g_buf_a + pfx_len, slen * 4U,
                          INFO_CODEC_FLAG_ALG, &ev_same);
    info_eval_stream_bits(&g_ws, g_buf_c, pfx_len, g_buf_a + pfx_len, slen * 4U,
                          INFO_CODEC_FLAG_ALG, &ev_diff);
    if (ev_same.total_bits_q12 >= ev_diff.total_bits_q12) {
        fails++;
    }
    return fails;
}

static uint32_t test_t8_t10_separation(void) {
    uint32_t fails = UINT32_C(0);
    info_sep_atlas_t sa;
    info_classify_separation(&g_ws, g_buf_a, g_buf_b, g_buf_c, sizeof(g_buf_b), &sa);
    /* T8: LFSR-23 pure ctx >= 7.5 bpb (30720 bits) vs full alg <= 0.15 bpb (614 bits) */
    if (sa.lfsr_roundtrip_ok != 1U || sa.lfsr_ctx_bits < 30720U || sa.lfsr_alg_bits > 614U ||
        sa.lfsr_hits < 30000U) {
        fails++;
    }
    /* T9: Rule-30 32-bit CA separation */
    if (sa.ca_roundtrip_ok != 1U || sa.ca_alg_bits > 614U || sa.ca_ctx_bits < 30720U ||
        sa.ca_hits < 30000U) {
        fails++;
    }
    /* T10: Affine Mod-65536 separation */
    if (sa.aff_roundtrip_ok != 1U || sa.aff_ctx_bits < 30720U || sa.aff_alg_bits > 614U ||
        sa.aff_hits < 30000U) {
        fails++;
    }
    return fails;
}

static uint32_t test_t11_t16_theory_and_certs(void) {
    uint32_t fails = UINT32_C(0);
    /* T11: CTW stationary & switching dominance + KT conservation */
    info_ctw_atlas_t ctw;
    info_classify_ctw(&ctw);
    if (ctw.kt_conservation_ok != 1U || ctw.switching_dominates_ok != 1U ||
        ctw.ctw_stat_bits_q12 >= ctw.kt_stat_bits_q12 ||
        ctw.sw_ctw_sw_bits_q12 >= ctw.ctw_sw_bits_q12) {
        fails++;
    }
    /* T12: Delsarte Krawtchouk dual LP verification & SEARU code bounds */
    info_delsarte_atlas_t da;
    info_classify_delsarte(&da);
    if (da.all_dual_ok != 1U || da.num_rows < 8U) {
        fails++;
    }
    if (info_krawtchouk_int(7U, 0U, 3U) != 1 || info_krawtchouk_int(7U, 1U, 3U) != 1 ||
        info_krawtchouk_int(7U, 2U, 3U) != -3) {
        fails++;
    }
    /* T13: Balke-Pearl + Causal MDL + obs equiv */
    info_causal_atlas_t ca;
    info_classify_causal(&g_ws, g_buf_a, g_buf_b, &ca);
    if (ca.bp_sound != 1U || ca.obs_equiv_verified != 1U || ca.causal_mdl_correct < 4U) {
        fails++;
    }
    /* T14: Online regime-change surprise spike detection */
    size_t sw_len = 1024U;
    for (size_t i = 0U; i < sw_len; i++) {
        g_buf_a[i] = (i < 512U) ? UINT8_C(0x41) : (uint8_t)(((i * 97U) ^ (i >> 2U)) & 0xFFU);
    }
    info_stream_eval_t ev_sw;
    info_eval_stream_bits(&g_ws, NULL, 0U, g_buf_a, sw_len, INFO_CODEC_FLAG_ALG, &ev_sw);
    if (ev_sw.spike_offset < 512U || ev_sw.spike_offset > 528U || ev_sw.max_surprise_q12 < 8192U) {
        fails++;
    }
    /* T15: All 5 hunt witnesses + linear FIR1 cert checks */
    info_hunt_alg_t ha;
    info_hunt_alg_blindspot(UINT64_C(0x1337), &g_ws, g_buf_a, g_buf_b, g_buf_c, sizeof(g_buf_b),
                            &ha);
    if (ha.roundtrip_ok != 1U || ha.full_alg_bytes >= ha.pure_ctx_bytes ||
        !info_cert_emit_alg_fir(&ha, NULL, &g_cert_ws) || !g_cert_ws.ir_eval_ok) {
        fails++;
    }
    info_hunt_ctw_t hc;
    info_hunt_ctw_switch(UINT64_C(0x1337), &hc);
    if (hc.sw_dominates != 1U || !info_cert_emit_ctw_fir(&hc, NULL, &g_cert_ws) ||
        !g_cert_ws.ir_eval_ok) {
        fails++;
    }
    info_hunt_delsarte_t hd;
    info_hunt_delsarte_gap(UINT64_C(0x73), &hd);
    if (hd.dual_ok != 1U || hd.searu_size < 16U ||
        !info_cert_emit_delsarte_fir(&hd, NULL, &g_cert_ws) || !g_cert_ws.ir_eval_ok) {
        fails++;
    }
    info_hunt_bp_t hb;
    info_hunt_balke_pearl(UINT64_C(0x42), &hb);
    if (hb.natural_bound_ok != 1U || !info_cert_emit_bp_fir(&hb, NULL, &g_cert_ws) ||
        !g_cert_ws.ir_eval_ok) {
        fails++;
    }
    info_hunt_causal_mdl_t hm;
    info_hunt_causal_mdl(UINT64_C(0x55), &g_ws, g_buf_a, g_buf_b, &hm);
    if (hm.dir_recovered != 1U || !info_cert_emit_causal_mdl_fir(&hm, NULL, &g_cert_ws) ||
        !g_cert_ws.ir_eval_ok) {
        fails++;
    }
    /* T16: InfoHeader64 zero-UB ABI schema size check (16,384 bytes) */
    if (sizeof(InfoArena) != 16384U || sizeof(InfoHeader64) != 64U || INFO_MAX_AUX != 222U) {
        fails++;
    }
    return fails;
}

static bool info_buf_contains(const uint8_t *hay, size_t hlen, const char *needle) {
    size_t nlen = strlen(needle);
    if (nlen == 0U || hlen < nlen) {
        return false;
    }
    for (size_t i = 0U; i + nlen <= hlen; i++) {
        if (memcmp(hay + i, needle, nlen) == 0) {
            return true;
        }
    }
    return false;
}

static uint32_t test_t17_alpha_mdl(void) {
    uint32_t fails = UINT32_C(0);
    static const char k_src_a[] =
        "/* ELE subsystem dispatch */\n"
        "uint64_t ele_eval_circuit(const uint32_t *ele_nodes, uint32_t ele_cnt) {\n"
        "    uint64_t ele_acc = 25173U;\n"
        "    for (uint32_t ele_i = 0; ele_i < ele_cnt; ele_i++) {\n"
        "        uint64_t ele_v = flow_ir_eval_u64(ele_nodes, ele_i & 31U);\n"
        "        ele_acc ^= (ele_v << 16U) | (ele_v >> 8U);\n"
        "    }\n"
        "    return ele_acc;\n"
        "}\n";
    static const char k_src_b[] =
        "/* ECON multi-line\n * clearing alternative */\n"
        "uint64_t econ_clear_book(const uint32_t *econ_orders, uint32_t econ_len) {\n"
        "    uint64_t econ_sum = 99991U;\n"
        "    for (uint32_t econ_k = 0; econ_k < econ_len; econ_k++) {\n"
        "        uint64_t econ_val = flow_ir_eval_u64(econ_orders, econ_k & 31U);\n"
        "        econ_sum ^= (econ_val << 16U) | (econ_val >> 8U);\n"
        "    }\n"
        "    return econ_sum;\n"
        "}\n";
    static const char k_unrel[] =
        "while (q_state != 0U) { if ((q_state & 1U) != 0U) { acc_x += 777U; } else { acc_y -= 333U; } q_state >>= 1U; }\n"
        "switch (mode_tag) { case 3: return \"alpha\"; case 5: return \"beta\"; case 7: return \"gamma\"; default: return \"delta\"; }\n";

    size_t half = INFO_CLI_MAX_BYTES >> 2U;
    uint8_t *c_a = g_buf_a;
    uint8_t *c_b = g_buf_b;
    uint8_t *c_idem = g_buf_c;
    uint8_t *c_unrel = g_buf_c + half;

    size_t l_a = info_alpha_canonicalize(&g_alpha_ws, (const uint8_t *)k_src_a, strlen(k_src_a),
                                         INFO_LANG_C, c_a, half);
    size_t l_b = info_alpha_canonicalize(&g_alpha_ws, (const uint8_t *)k_src_b, strlen(k_src_b),
                                         INFO_LANG_C, c_b, half);
    size_t l_idem = info_alpha_canonicalize(&g_alpha_ws, c_a, l_a, INFO_LANG_C, c_idem, half);
    size_t l_unrel = info_alpha_canonicalize(&g_alpha_ws, (const uint8_t *)k_unrel, strlen(k_unrel),
                                             INFO_LANG_C, c_unrel, half);

    if (l_a == 0U || l_a != l_b || !info_mem_eq(c_a, c_b, l_a)) {
        fails++;
    }
    if (l_idem != l_a || !info_mem_eq(c_a, c_idem, l_a)) {
        fails++;
    }
    if (!info_buf_contains(c_a, l_a, "flow_ir_eval_u64") || info_buf_contains(c_a, l_a, "ele_") ||
        info_buf_contains(c_a, l_a, "/*")) {
        fails++;
    }

    const uint8_t *clones[3] = {c_a, c_b, c_idem};
    size_t clone_lens[3] = {l_a, l_b, l_idem};
    info_joint_mdl_t jm_good, jm_bad;
    info_eval_joint_mdl(&g_ws, clones, clone_lens, 3U, c_a, l_a, INFO_CODEC_FLAG_ALG, &jm_good);
    if (jm_good.joint_savings_bits_q12 <= 0 || jm_good.extract_gain_bits_q12 <= 0) {
        fails++;
    }
    info_eval_joint_mdl(&g_ws, clones, clone_lens, 2U, c_unrel, l_unrel, INFO_CODEC_FLAG_ALG,
                        &jm_bad);
    if (jm_bad.extract_gain_bits_q12 >= 0) {
        fails++;
    }
    return fails;
}

static uint32_t test_t18_lean_expr_alpha(void) {
    uint32_t fails = UINT32_C(0);
    static const char k_expr_a[] = "THM C_Alpha.thm : AP FA PROP C_Alpha.add BV0\n"
                                   "AP LM BV0 AP C_Alpha.add C_Alpha.zero\n";
    static const char k_expr_b[] = "THM C_Beta.lem : AP FA PROP C_Beta.mul BV0\n"
                                   "AP LM BV0 AP C_Beta.mul C_Gamma.one\n";
    static const char k_expr_unrel[] = "DEF C_Delta.fn : LT LV0 ST bv AP BV2 BV3\n"
                                       "AP AP BV1 AP C_Delta.g BV0\n";

    size_t half = INFO_CLI_MAX_BYTES >> 2U;
    uint8_t *e_a = g_buf_a;
    uint8_t *e_b = g_buf_b;
    uint8_t *e_c = g_buf_c;
    uint8_t *e_u = g_buf_c + half;

    size_t l_a = info_alpha_canonicalize(&g_alpha_ws, (const uint8_t *)k_expr_a, strlen(k_expr_a),
                                         INFO_LANG_LEAN_EXPR, e_a, half);
    size_t l_b = info_alpha_canonicalize(&g_alpha_ws, (const uint8_t *)k_expr_b, strlen(k_expr_b),
                                         INFO_LANG_LEAN_EXPR, e_b, half);
    size_t l_c = info_alpha_canonicalize(&g_alpha_ws, e_a, l_a, INFO_LANG_LEAN_EXPR, e_c, half);
    size_t l_u = info_alpha_canonicalize(&g_alpha_ws, (const uint8_t *)k_expr_unrel,
                                         strlen(k_expr_unrel), INFO_LANG_LEAN_EXPR, e_u, half);

    if (l_a == 0U || l_a != l_b || !info_mem_eq(e_a, e_b, l_a) || l_c != l_a ||
        !info_mem_eq(e_a, e_c, l_a)) {
        fails++;
    }
    if (!info_buf_contains(e_a, l_a, "AP") || !info_buf_contains(e_a, l_a, "BV0") ||
        info_buf_contains(e_a, l_a, "C_Alpha")) {
        fails++;
    }

    const uint8_t *clones[3] = {e_a, e_b, e_c};
    size_t clone_lens[3] = {l_a, l_b, l_c};
    info_joint_mdl_t jm_good, jm_bad;
    info_eval_joint_mdl(&g_ws, clones, clone_lens, 3U, e_a, l_a, INFO_CODEC_FLAG_ALG, &jm_good);
    info_eval_joint_mdl(&g_ws, clones, clone_lens, 2U, e_u, l_u, INFO_CODEC_FLAG_ALG, &jm_bad);
    if (jm_good.extract_gain_bits_q12 <= 0 || jm_bad.extract_gain_bits_q12 >= 0) {
        fails++;
    }
    return fails;
}

static int info_cmd_selftest(void) {
    uint32_t f_prim = test_t1_t4_primitives();
    uint32_t f_codec = test_t5_t7_codec_roundtrip();
    uint32_t f_sep = test_t8_t10_separation();
    uint32_t f_thy = test_t11_t16_theory_and_certs();
    uint32_t f_mdl = test_t17_alpha_mdl() + test_t18_lean_expr_alpha();
    uint32_t total = f_prim + f_codec + f_sep + f_thy + f_mdl;
    printf("[selftest] T1..T4(prim)=%s T5..T7(codec)=%s T8..T10(alg_sep)=%s "
           "T11..T18(ctw/delsarte/causal/fir/alpha_mdl/lean_expr)=%s | fails=%u\n",
           f_prim == 0U ? "PASS" : "FAIL", f_codec == 0U ? "PASS" : "FAIL",
           f_sep == 0U ? "PASS" : "FAIL", (f_thy + f_mdl) == 0U ? "PASS" : "FAIL", (unsigned)total);
    return (total == 0U) ? 0 : 1;
}

/* ============================================================================
 * CLI Commands
 * ============================================================================ */

static int info_cmd_compress(int argc, char **argv) {
    const char *in_p = argv[2];
    const char *out_p = argv[3];
    uint32_t flags = info_has_flag(argc, argv, 4, "--no-alg") ? UINT32_C(0) : INFO_CODEC_FLAG_ALG;
    size_t len = 0U;
    if (!info_read_file(in_p, g_buf_a, INFO_CLI_MAX_BYTES, &len)) {
        (void)fprintf(stderr, "ERROR: cannot read %s (or exceeds 4MB)\n", in_p);
        return 1;
    }
    size_t cmp_len = info_compress(&g_ws, g_buf_a, len, g_buf_b, sizeof(g_buf_b), flags);
    if (cmp_len == 0U || !info_write_file(out_p, g_buf_b, cmp_len)) {
        (void)fprintf(stderr, "ERROR: compress/write failed\n");
        return 1;
    }
    printf("[compress] in=%zuB out=%zuB flags=%u\n", len, cmp_len, (unsigned)flags);
    return 0;
}

static int info_cmd_decompress(const char *in_p, const char *out_p) {
    size_t len = 0U;
    if (!info_read_file(in_p, g_buf_a, sizeof(g_buf_a), &len)) {
        (void)fprintf(stderr, "ERROR: cannot read %s\n", in_p);
        return 1;
    }
    size_t dec_len = info_decompress(&g_ws, g_buf_a, len, g_buf_b, INFO_CLI_MAX_BYTES);
    if (dec_len == SIZE_MAX || !info_write_file(out_p, g_buf_b, dec_len)) {
        (void)fprintf(stderr, "ERROR: decompress failed\n");
        return 1;
    }
    printf("[decompress] in=%zuB out=%zuB\n", len, dec_len);
    return 0;
}

static int info_cmd_eval_bpb(int argc, char **argv) {
    const char *in_p = argv[2];
    uint32_t flags = info_has_flag(argc, argv, 3, "--no-alg") ? UINT32_C(0) : INFO_CODEC_FLAG_ALG;
    const char *out_json = info_parse_opt(argc, argv, 3, "--out-json");
    size_t len = 0U;
    if (!info_read_file(in_p, g_buf_a, INFO_CLI_MAX_BYTES, &len)) {
        (void)fprintf(stderr, "ERROR: cannot read %s\n", in_p);
        return 1;
    }
    info_stream_eval_t ev;
    info_eval_stream_bits(&g_ws, NULL, 0U, g_buf_a, len, flags, &ev);
    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"orig_bytes\": %llu,\n"
                "  \"total_bits_q12\": %llu,\n"
                "  \"alg_hits\": %llu,\n"
                "  \"match_hits\": %llu,\n"
                "  \"max_surprise_q12\": %llu,\n"
                "  \"spike_offset\": %llu,\n"
                "  \"f0_bits_q12\": %llu,\n"
                "  \"f1_bits_q12\": %llu,\n"
                "  \"fnv1a\": \"0x%016llx\"\n"
                "}\n",
                (unsigned long long)ev.orig_bytes, (unsigned long long)ev.total_bits_q12,
                (unsigned long long)ev.alg_hits, (unsigned long long)ev.match_hits,
                (unsigned long long)ev.max_surprise_q12, (unsigned long long)ev.spike_offset,
                (unsigned long long)ev.f0_bits_q12, (unsigned long long)ev.f1_bits_q12,
                (unsigned long long)ev.payload_fnv);
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[eval-bpb] bytes=%llu bits_q12=%llu alg_hits=%llu spike_off=%llu\n",
           (unsigned long long)ev.orig_bytes, (unsigned long long)ev.total_bits_q12,
           (unsigned long long)ev.alg_hits, (unsigned long long)ev.spike_offset);
    return 0;
}

static int info_cmd_ncd(int argc, char **argv) {
    const char *p_a = argv[2];
    const char *p_b = argv[3];
    const char *out_json = info_parse_opt(argc, argv, 4, "--out-json");
    size_t la = 0U;
    size_t lb = 0U;
    if (!info_read_file(p_a, g_buf_a, INFO_CLI_MAX_BYTES >> 1U, &la) ||
        !info_read_file(p_b, g_buf_b, INFO_CLI_MAX_BYTES >> 1U, &lb)) {
        (void)fprintf(stderr, "ERROR: cannot read %s or %s\n", p_a, p_b);
        return 1;
    }
    info_stream_eval_t ea, eb, eba, eab;
    info_eval_stream_bits(&g_ws, NULL, 0U, g_buf_a, la, INFO_CODEC_FLAG_ALG, &ea);
    info_eval_stream_bits(&g_ws, NULL, 0U, g_buf_b, lb, INFO_CODEC_FLAG_ALG, &eb);
    info_eval_stream_bits(&g_ws, g_buf_a, la, g_buf_b, lb, INFO_CODEC_FLAG_ALG, &eba);
    info_eval_stream_bits(&g_ws, g_buf_b, lb, g_buf_a, la, INFO_CODEC_FLAG_ALG, &eab);

    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"len_a\": %zu,\n"
                "  \"len_b\": %zu,\n"
                "  \"la_bits_q12\": %llu,\n"
                "  \"lb_bits_q12\": %llu,\n"
                "  \"lb_given_a_bits_q12\": %llu,\n"
                "  \"la_given_b_bits_q12\": %llu\n"
                "}\n",
                la, lb, (unsigned long long)ea.total_bits_q12,
                (unsigned long long)eb.total_bits_q12, (unsigned long long)eba.total_bits_q12,
                (unsigned long long)eab.total_bits_q12);
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[ncd] la_q12=%llu lb_q12=%llu lb|a_q12=%llu la|b_q12=%llu\n",
           (unsigned long long)ea.total_bits_q12, (unsigned long long)eb.total_bits_q12,
           (unsigned long long)eba.total_bits_q12, (unsigned long long)eab.total_bits_q12);
    return 0;
}

static int info_cmd_causal_mdl(int argc, char **argv) {
    const char *p_x = argv[2];
    const char *p_y = argv[3];
    const char *out_json = info_parse_opt(argc, argv, 4, "--out-json");
    size_t lx = 0U;
    size_t ly = 0U;
    if (!info_read_file(p_x, g_buf_a, INFO_CLI_MAX_BYTES >> 2U, &lx) ||
        !info_read_file(p_y, g_buf_b, INFO_CLI_MAX_BYTES >> 2U, &ly) || lx != ly || lx == 0U) {
        (void)fprintf(stderr, "ERROR: invalid pair files %s / %s\n", p_x, p_y);
        return 1;
    }
    /* Interleave (x, y) into g_buf_c and evaluate even (X) and odd (Y|X) bit costs */
    for (size_t i = 0U; i < lx; i++) {
        g_buf_c[2U * i] = g_buf_a[i];
        g_buf_c[2U * i + 1U] = g_buf_b[i];
    }
    size_t c_fwd = info_compress(&g_ws, g_buf_c, 2U * lx, g_buf_b + lx, sizeof(g_buf_b) - lx,
                                 INFO_CODEC_FLAG_ALG);
    /* Reverse interleave (y, x) */
    for (size_t i = 0U; i < lx; i++) {
        g_buf_c[2U * i] = g_buf_b[i];
        g_buf_c[2U * i + 1U] = g_buf_a[i];
    }
    size_t c_rev = info_compress(&g_ws, g_buf_c, 2U * lx, g_buf_b + lx, sizeof(g_buf_b) - lx,
                                 INFO_CODEC_FLAG_ALG);
    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"pairs\": %zu,\n"
                "  \"fwd_xy_bytes\": %zu,\n"
                "  \"rev_yx_bytes\": %zu,\n"
                "  \"predicted_dir\": \"%s\"\n"
                "}\n",
                lx, c_fwd, c_rev, (c_fwd < c_rev) ? "X->Y" : ((c_rev < c_fwd) ? "Y->X" : "TIE"));
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[causal-mdl] n=%zu fwd_xy=%zuB rev_yx=%zuB dir=%s\n", lx, c_fwd, c_rev,
           (c_fwd < c_rev) ? "X->Y" : ((c_rev < c_fwd) ? "Y->X" : "TIE"));
    return 0;
}

static int info_cmd_classify_ctw(const char *out_json) {
    info_ctw_atlas_t a;
    info_classify_ctw(&a);
    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"stationary_bytes\": %llu,\n"
                "  \"kt_stat_bits_q12\": %llu,\n"
                "  \"ctw_stat_bits_q12\": %llu,\n"
                "  \"sw_ctw_stat_bits_q12\": %llu,\n"
                "  \"switching_bytes\": %llu,\n"
                "  \"kt_sw_bits_q12\": %llu,\n"
                "  \"ctw_sw_bits_q12\": %llu,\n"
                "  \"sw_ctw_sw_bits_q12\": %llu,\n"
                "  \"kt_conservation_ok\": %u,\n"
                "  \"switching_dominates_ok\": %u\n"
                "}\n",
                (unsigned long long)a.stationary_bytes, (unsigned long long)a.kt_stat_bits_q12,
                (unsigned long long)a.ctw_stat_bits_q12, (unsigned long long)a.sw_ctw_stat_bits_q12,
                (unsigned long long)a.switching_bytes, (unsigned long long)a.kt_sw_bits_q12,
                (unsigned long long)a.ctw_sw_bits_q12, (unsigned long long)a.sw_ctw_sw_bits_q12,
                (unsigned)a.kt_conservation_ok, (unsigned)a.switching_dominates_ok);
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[classify-ctw] stat(kt=%llu ctw=%llu) sw(ctw=%llu sw_ctw=%llu) cons=%u dom=%u\n",
           (unsigned long long)(a.kt_stat_bits_q12 >> 12U),
           (unsigned long long)(a.ctw_stat_bits_q12 >> 12U),
           (unsigned long long)(a.ctw_sw_bits_q12 >> 12U),
           (unsigned long long)(a.sw_ctw_sw_bits_q12 >> 12U), (unsigned)a.kt_conservation_ok,
           (unsigned)a.switching_dominates_ok);
    return 0;
}

static int info_cmd_classify_separation(const char *out_json) {
    info_sep_atlas_t a;
    info_classify_separation(&g_ws, g_buf_a, g_buf_b, g_buf_c, sizeof(g_buf_b), &a);
    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"stream_bytes\": %llu,\n"
                "  \"lfsr_ctx_bits\": %llu,\n"
                "  \"lfsr_alg_bits\": %llu,\n"
                "  \"lfsr_hits\": %llu,\n"
                "  \"lfsr_roundtrip_ok\": %u,\n"
                "  \"ca_ctx_bits\": %llu,\n"
                "  \"ca_alg_bits\": %llu,\n"
                "  \"ca_hits\": %llu,\n"
                "  \"ca_roundtrip_ok\": %u,\n"
                "  \"aff_ctx_bits\": %llu,\n"
                "  \"aff_alg_bits\": %llu,\n"
                "  \"aff_hits\": %llu,\n"
                "  \"aff_roundtrip_ok\": %u\n"
                "}\n",
                (unsigned long long)a.stream_bytes, (unsigned long long)a.lfsr_ctx_bits,
                (unsigned long long)a.lfsr_alg_bits, (unsigned long long)a.lfsr_hits,
                (unsigned)a.lfsr_roundtrip_ok, (unsigned long long)a.ca_ctx_bits,
                (unsigned long long)a.ca_alg_bits, (unsigned long long)a.ca_hits,
                (unsigned)a.ca_roundtrip_ok, (unsigned long long)a.aff_ctx_bits,
                (unsigned long long)a.aff_alg_bits, (unsigned long long)a.aff_hits,
                (unsigned)a.aff_roundtrip_ok);
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[classify-separation] lfsr(%llu->%llu b) ca(%llu->%llu b) aff(%llu->%llu b)\n",
           (unsigned long long)a.lfsr_ctx_bits, (unsigned long long)a.lfsr_alg_bits,
           (unsigned long long)a.ca_ctx_bits, (unsigned long long)a.ca_alg_bits,
           (unsigned long long)a.aff_ctx_bits, (unsigned long long)a.aff_alg_bits);
    return 0;
}

static int info_cmd_classify_delsarte(const char *out_json) {
    info_delsarte_atlas_t a;
    info_classify_delsarte(&a);
    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp, "{\n  \"num_rows\": %u,\n  \"all_dual_ok\": %u,\n  \"rows\": [\n",
                (unsigned)a.num_rows, (unsigned)a.all_dual_ok);
        for (uint32_t i = 0U; i < a.num_rows; i++) {
            const info_delsarte_row_t *r = &a.rows[i];
            fprintf(fp,
                    "    {\"n\": %u, \"d\": %u, \"searu_size\": %llu, \"singleton_ub\": %llu, "
                    "\"hamming_ub\": %llu, \"plotkin_ub\": %llu, \"delsarte_num\": %llu, "
                    "\"delsarte_den\": %llu, \"dual_ok\": %u, \"tight\": %u}%s\n",
                    (unsigned)r->n, (unsigned)r->d, (unsigned long long)r->searu_code_size,
                    (unsigned long long)r->singleton_ub, (unsigned long long)r->hamming_ub,
                    (unsigned long long)r->plotkin_ub, (unsigned long long)r->delsarte_ub_num,
                    (unsigned long long)r->delsarte_ub_den, (unsigned)r->dual_verified,
                    (unsigned)r->tight, (i + 1U < a.num_rows) ? "," : "");
        }
        fprintf(fp, "  ]\n}\n");
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[classify-delsarte] rows=%u all_dual_ok=%u A(7,3)_searu=%llu\n", (unsigned)a.num_rows,
           (unsigned)a.all_dual_ok, (unsigned long long)a.rows[3].searu_code_size);
    return 0;
}

static int info_cmd_classify_causal(const char *out_json) {
    info_causal_atlas_t a;
    info_classify_causal(&g_ws, g_buf_a, g_buf_b, &a);
    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"bp_low_num\": %lld,\n"
                "  \"bp_high_num\": %lld,\n"
                "  \"bp_den\": %llu,\n"
                "  \"bp_true_num\": %lld,\n"
                "  \"bp_sound\": %u,\n"
                "  \"obs_equiv_verified\": %u,\n"
                "  \"causal_mdl_pairs_tested\": %u,\n"
                "  \"causal_mdl_correct\": %u,\n"
                "  \"sym_joint_blind_count\": %u\n"
                "}\n",
                (long long)a.bp_low_num, (long long)a.bp_high_num, (unsigned long long)a.bp_den,
                (long long)a.bp_true_num, (unsigned)a.bp_sound, (unsigned)a.obs_equiv_verified,
                (unsigned)a.causal_mdl_pairs_tested, (unsigned)a.causal_mdl_correct,
                (unsigned)a.sym_joint_blind_count);
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[classify-causal] bp=[%lld,%lld]/%llu sound=%u causal_mdl=%u/%u\n",
           (long long)a.bp_low_num, (long long)a.bp_high_num, (unsigned long long)a.bp_den,
           (unsigned)a.bp_sound, (unsigned)a.causal_mdl_correct,
           (unsigned)a.causal_mdl_pairs_tested);
    return 0;
}

static int info_cmd_hunt(int argc, char **argv) {
    const char *mode = argv[2];
    const char *seed_s = info_parse_opt(argc, argv, 3, "--seed");
    const char *out_lean = info_parse_opt(argc, argv, 3, "--out-lean");
    const char *out_fir = info_parse_opt(argc, argv, 3, "--out-fir");
    const char *out_json = info_parse_opt(argc, argv, 3, "--out-json");
    uint64_t seed = UINT64_C(0x1337);
    if (seed_s != NULL && !info_parse_u64(seed_s, &seed)) {
        (void)fprintf(stderr, "ERROR: invalid --seed\n");
        return 1;
    }

    if (info_cstr_eq(mode, "alg-blindspot")) {
        info_hunt_alg_t w;
        info_hunt_alg_blindspot(seed, &g_ws, g_buf_a, g_buf_b, g_buf_c, sizeof(g_buf_b), &w);
        if (!info_cert_emit_alg_fir(&w, out_fir, &g_cert_ws)) {
            return 1;
        }
        if (out_lean != NULL && !info_cert_emit_alg_lean(&w, out_lean)) {
            return 1;
        }
        if (out_json != NULL && !info_cert_emit_alg_json(&w, &g_cert_ws, out_json)) {
            return 1;
        }
        printf("[hunt alg-blindspot] ctx=%lluB alg=%lluB hits=%llu merkle=0x%016llx\n",
               (unsigned long long)w.pure_ctx_bytes, (unsigned long long)w.full_alg_bytes,
               (unsigned long long)w.alg_hits, (unsigned long long)w.merkle);
        return 0;
    }
    if (info_cstr_eq(mode, "ctw-switch")) {
        info_hunt_ctw_t w;
        info_hunt_ctw_switch(seed, &w);
        if (!info_cert_emit_ctw_fir(&w, out_fir, &g_cert_ws)) {
            return 1;
        }
        if (out_lean != NULL && !info_cert_emit_ctw_lean(&w, out_lean)) {
            return 1;
        }
        if (out_json != NULL && !info_cert_emit_ctw_json(&w, &g_cert_ws, out_json)) {
            return 1;
        }
        printf("[hunt ctw-switch] ctw=%llu sw=%llu dom=%u merkle=0x%016llx\n",
               (unsigned long long)w.ctw_bits_q12, (unsigned long long)w.sw_bits_q12,
               (unsigned)w.sw_dominates, (unsigned long long)w.merkle);
        return 0;
    }
    if (info_cstr_eq(mode, "delsarte-gap")) {
        info_hunt_delsarte_t w;
        info_hunt_delsarte_gap(seed, &w);
        if (!info_cert_emit_delsarte_fir(&w, out_fir, &g_cert_ws)) {
            return 1;
        }
        if (out_lean != NULL && !info_cert_emit_delsarte_lean(&w, out_lean)) {
            return 1;
        }
        if (out_json != NULL && !info_cert_emit_delsarte_json(&w, &g_cert_ws, out_json)) {
            return 1;
        }
        printf("[hunt delsarte-gap] n=%u d=%u searu=%llu ub=%llu/%llu dual=%u\n", (unsigned)w.n,
               (unsigned)w.d, (unsigned long long)w.searu_size, (unsigned long long)w.delsarte_num,
               (unsigned long long)w.delsarte_den, (unsigned)w.dual_ok);
        return 0;
    }
    if (info_cstr_eq(mode, "balke-pearl")) {
        info_hunt_bp_t w;
        info_hunt_balke_pearl(seed, &w);
        if (!info_cert_emit_bp_fir(&w, out_fir, &g_cert_ws)) {
            return 1;
        }
        if (out_lean != NULL && !info_cert_emit_bp_lean(&w, out_lean)) {
            return 1;
        }
        if (out_json != NULL && !info_cert_emit_bp_json(&w, &g_cert_ws, out_json)) {
            return 1;
        }
        printf("[hunt balke-pearl] interval=[%lld,%lld]/%llu true=%lld ok=%u\n",
               (long long)w.low_num, (long long)w.high_num, (unsigned long long)w.den,
               (long long)w.true_num, (unsigned)w.natural_bound_ok);
        return 0;
    }
    if (info_cstr_eq(mode, "causal-mdl")) {
        info_hunt_causal_mdl_t w;
        info_hunt_causal_mdl(seed, &g_ws, g_buf_a, g_buf_b, &w);
        if (!info_cert_emit_causal_mdl_fir(&w, out_fir, &g_cert_ws)) {
            return 1;
        }
        if (out_lean != NULL && !info_cert_emit_causal_mdl_lean(&w, out_lean)) {
            return 1;
        }
        if (out_json != NULL && !info_cert_emit_causal_mdl_json(&w, &g_cert_ws, out_json)) {
            return 1;
        }
        printf("[hunt causal-mdl] lxy_q12=%llu lyx_q12=%llu ok=%u\n",
               (unsigned long long)w.lxy_total_q12, (unsigned long long)w.lyx_total_q12,
               (unsigned)w.dir_recovered);
        return 0;
    }
    (void)fprintf(stderr, "ERROR: unknown hunt mode '%s'\n", mode);
    return 1;
}

static uint32_t info_parse_lang(const char *s) {
    if (s == NULL || info_cstr_eq(s, "raw")) {
        return INFO_LANG_RAW;
    }
    if (info_cstr_eq(s, "c")) {
        return INFO_LANG_C;
    }
    if (info_cstr_eq(s, "lean")) {
        return INFO_LANG_LEAN;
    }
    if (info_cstr_eq(s, "py")) {
        return INFO_LANG_PY;
    }
    if (info_cstr_eq(s, "expr")) {
        return INFO_LANG_LEAN_EXPR;
    }
    return INFO_LANG_RAW;
}

static int info_cmd_alpha_canon(int argc, char **argv) {
    const char *in_p = argv[2];
    const char *out_p = argv[3];
    const char *lang_s = info_parse_opt(argc, argv, 4, "--lang");
    uint32_t lang = info_parse_lang(lang_s);
    size_t len = 0U;
    if (!info_read_file(in_p, g_buf_a, INFO_CLI_MAX_BYTES >> 1U, &len)) {
        (void)fprintf(stderr, "ERROR: cannot read %s\n", in_p);
        return 1;
    }
    size_t clen =
        info_alpha_canonicalize(&g_alpha_ws, g_buf_a, len, lang, g_buf_b, sizeof(g_buf_b));
    if (!info_write_file(out_p, g_buf_b, clen)) {
        (void)fprintf(stderr, "ERROR: cannot write %s\n", out_p);
        return 1;
    }
    printf("[alpha-canon] in=%zuB out=%zuB unique_ids=%u\n", len, clen,
           (unsigned)g_alpha_ws.unique_ids);
    return 0;
}

static int info_cmd_alpha_ncd(int argc, char **argv) {
    const char *p_a = argv[2];
    const char *p_b = argv[3];
    const char *lang_s = info_parse_opt(argc, argv, 4, "--lang");
    const char *out_json = info_parse_opt(argc, argv, 4, "--out-json");
    uint32_t lang = info_parse_lang(lang_s);
    size_t max_in = INFO_CLI_MAX_BYTES >> 2U;
    size_t la = 0U;
    size_t lb = 0U;
    if (!info_read_file(p_a, g_buf_a, max_in, &la) || !info_read_file(p_b, g_buf_b, max_in, &lb)) {
        (void)fprintf(stderr, "ERROR: cannot read %s or %s\n", p_a, p_b);
        return 1;
    }
    info_stream_eval_t r_a, r_b, r_ba, r_ab;
    info_eval_stream_bits(&g_ws, NULL, 0U, g_buf_a, la, INFO_CODEC_FLAG_ALG, &r_a);
    info_eval_stream_bits(&g_ws, NULL, 0U, g_buf_b, lb, INFO_CODEC_FLAG_ALG, &r_b);
    info_eval_stream_bits(&g_ws, g_buf_a, la, g_buf_b, lb, INFO_CODEC_FLAG_ALG, &r_ba);
    info_eval_stream_bits(&g_ws, g_buf_b, lb, g_buf_a, la, INFO_CODEC_FLAG_ALG, &r_ab);

    size_t slot_cap = INFO_CLI_MAX_BYTES >> 1U;
    uint8_t *ca = g_buf_c;
    uint8_t *cb = g_buf_c + slot_cap;
    size_t cla = info_alpha_canonicalize(&g_alpha_ws, g_buf_a, la, lang, ca, slot_cap);
    uint32_t ids_a = g_alpha_ws.unique_ids;
    size_t clb = info_alpha_canonicalize(&g_alpha_ws, g_buf_b, lb, lang, cb, slot_cap);
    uint32_t ids_b = g_alpha_ws.unique_ids;

    info_stream_eval_t a_a, a_b, a_ba, a_ab;
    info_eval_stream_bits(&g_ws, NULL, 0U, ca, cla, INFO_CODEC_FLAG_ALG, &a_a);
    info_eval_stream_bits(&g_ws, NULL, 0U, cb, clb, INFO_CODEC_FLAG_ALG, &a_b);
    info_eval_stream_bits(&g_ws, ca, cla, cb, clb, INFO_CODEC_FLAG_ALG, &a_ba);
    info_eval_stream_bits(&g_ws, cb, clb, ca, cla, INFO_CODEC_FLAG_ALG, &a_ab);

    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"raw_la_q12\": %llu,\n"
                "  \"raw_lb_q12\": %llu,\n"
                "  \"raw_lba_q12\": %llu,\n"
                "  \"raw_lab_q12\": %llu,\n"
                "  \"alpha_len_a\": %zu,\n"
                "  \"alpha_len_b\": %zu,\n"
                "  \"alpha_ids_a\": %u,\n"
                "  \"alpha_ids_b\": %u,\n"
                "  \"alpha_la_q12\": %llu,\n"
                "  \"alpha_lb_q12\": %llu,\n"
                "  \"alpha_lba_q12\": %llu,\n"
                "  \"alpha_lab_q12\": %llu\n"
                "}\n",
                (unsigned long long)r_a.total_bits_q12, (unsigned long long)r_b.total_bits_q12,
                (unsigned long long)r_ba.total_bits_q12, (unsigned long long)r_ab.total_bits_q12,
                cla, clb, (unsigned)ids_a, (unsigned)ids_b, (unsigned long long)a_a.total_bits_q12,
                (unsigned long long)a_b.total_bits_q12, (unsigned long long)a_ba.total_bits_q12,
                (unsigned long long)a_ab.total_bits_q12);
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[alpha-ncd] raw_ba_q12=%llu alpha_ba_q12=%llu alpha_ab_q12=%llu\n",
           (unsigned long long)r_ba.total_bits_q12, (unsigned long long)a_ba.total_bits_q12,
           (unsigned long long)a_ab.total_bits_q12);
    return 0;
}

static int info_cmd_eval_mdl_group(int argc, char **argv) {
    bool use_alpha = info_has_flag(argc, argv, 2, "--alpha");
    uint32_t lang = info_parse_lang(info_parse_opt(argc, argv, 2, "--lang"));
    const char *shared_p = info_parse_opt(argc, argv, 2, "--shared");
    const char *out_json = info_parse_opt(argc, argv, 2, "--out-json");

    const uint8_t *ptrs[16];
    size_t lens[16];
    uint32_t count = UINT32_C(0);
    size_t pack_off = 0U;

    for (int i = 2; i < argc; i++) {
        if (info_cstr_eq(argv[i], "--alpha")) {
            continue;
        }
        if (info_cstr_eq(argv[i], "--lang") || info_cstr_eq(argv[i], "--shared") ||
            info_cstr_eq(argv[i], "--out-json")) {
            i++;
            continue;
        }
        if (count >= 16U) {
            (void)fprintf(stderr, "ERROR: too many group files (max 16)\n");
            return 1;
        }
        size_t flen = 0U;
        if (!info_read_file(argv[i], g_buf_a, INFO_CLI_MAX_BYTES >> 2U, &flen)) {
            (void)fprintf(stderr, "ERROR: cannot read %s\n", argv[i]);
            return 1;
        }
        if (pack_off >= INFO_CLI_MAX_BYTES) {
            (void)fprintf(stderr, "ERROR: group buffer full\n");
            return 1;
        }
        size_t rem = INFO_CLI_MAX_BYTES - pack_off;
        size_t stored = 0U;
        if (use_alpha) {
            stored =
                info_alpha_canonicalize(&g_alpha_ws, g_buf_a, flen, lang, g_buf_b + pack_off, rem);
        } else {
            if (flen > rem) {
                (void)fprintf(stderr, "ERROR: group buffer overflow\n");
                return 1;
            }
            memcpy(g_buf_b + pack_off, g_buf_a, flen);
            stored = flen;
        }
        ptrs[count] = g_buf_b + pack_off;
        lens[count] = stored;
        pack_off += stored;
        count++;
    }
    if (count == 0U) {
        (void)fprintf(stderr, "ERROR: eval-mdl-group requires >= 1 input file\n");
        return 1;
    }

    const uint8_t *shared_ptr = NULL;
    size_t shared_len = 0U;
    if (shared_p != NULL) {
        size_t slen = 0U;
        if (!info_read_file(shared_p, g_buf_a, INFO_CLI_MAX_BYTES >> 1U, &slen)) {
            (void)fprintf(stderr, "ERROR: cannot read --shared %s\n", shared_p);
            return 1;
        }
        if (use_alpha) {
            shared_len = info_alpha_canonicalize(&g_alpha_ws, g_buf_a, slen, lang, g_buf_c,
                                                 INFO_CLI_MAX_BYTES);
        } else {
            memcpy(g_buf_c, g_buf_a, slen);
            shared_len = slen;
        }
        shared_ptr = g_buf_c;
    }

    info_joint_mdl_t jm;
    info_eval_joint_mdl(&g_ws, ptrs, lens, count, shared_ptr, shared_len, INFO_CODEC_FLAG_ALG, &jm);

    if (out_json != NULL) {
        FILE *fp = fopen(out_json, "wb");
        if (fp == NULL) {
            return 1;
        }
        fprintf(fp,
                "{\n"
                "  \"count\": %u,\n"
                "  \"sum_indep_bits_q12\": %llu,\n"
                "  \"seq_joint_bits_q12\": %llu,\n"
                "  \"shared_bits_q12\": %llu,\n"
                "  \"sum_cond_shared_bits_q12\": %llu,\n"
                "  \"joint_savings_bits_q12\": %lld,\n"
                "  \"extract_gain_bits_q12\": %lld\n"
                "}\n",
                (unsigned)jm.count, (unsigned long long)jm.sum_indep_bits_q12,
                (unsigned long long)jm.seq_joint_bits_q12, (unsigned long long)jm.shared_bits_q12,
                (unsigned long long)jm.sum_cond_shared_bits_q12,
                (long long)jm.joint_savings_bits_q12, (long long)jm.extract_gain_bits_q12);
        if (fclose(fp) != 0) {
            return 1;
        }
    }
    printf("[eval-mdl-group] n=%u indep_q12=%llu seq_q12=%llu extract_gain_q12=%lld\n",
           (unsigned)jm.count, (unsigned long long)jm.sum_indep_bits_q12,
           (unsigned long long)jm.seq_joint_bits_q12, (long long)jm.extract_gain_bits_q12);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        (void)fprintf(
            stderr,
            "Usage:\n  info selftest\n  info compress <in> <out.inf> [--no-alg]\n"
            "  info decompress <in.inf> <out>\n  info eval-bpb <in> [--no-alg] [--out-json <p>]\n"
            "  info ncd <file_a> <file_b> [--out-json <p>]\n"
            "  info alpha-canon <in> <out> [--lang raw|c|lean|py|expr]\n"
            "  info alpha-ncd <file_a> <file_b> [--lang raw|c|lean|py|expr] [--out-json <p>]\n"
            "  info eval-mdl-group [--alpha] [--lang raw|c|lean|py|expr] [--shared <m>] "
            "[--out-json <p>] <f1> ...\n"
            "  info causal-mdl <x_file> <y_file> [--out-json <p>]\n"
            "  info classify-<ctw|separation|delsarte|causal> [--out-json <p>]\n"
            "  info hunt <alg-blindspot|ctw-switch|delsarte-gap|balke-pearl|causal-mdl> "
            "[--seed <u64>] [--out-lean <p>] [--out-fir <p>] [--out-json <p>]\n");
        return 1;
    }
    if (info_cstr_eq(argv[1], "selftest")) {
        return info_cmd_selftest();
    }
    if (info_cstr_eq(argv[1], "compress") && argc >= 4) {
        return info_cmd_compress(argc, argv);
    }
    if (info_cstr_eq(argv[1], "decompress") && argc >= 4) {
        return info_cmd_decompress(argv[2], argv[3]);
    }
    if (info_cstr_eq(argv[1], "eval-bpb") && argc >= 3) {
        return info_cmd_eval_bpb(argc, argv);
    }
    if (info_cstr_eq(argv[1], "ncd") && argc >= 4) {
        return info_cmd_ncd(argc, argv);
    }
    if (info_cstr_eq(argv[1], "alpha-canon") && argc >= 4) {
        return info_cmd_alpha_canon(argc, argv);
    }
    if (info_cstr_eq(argv[1], "alpha-ncd") && argc >= 4) {
        return info_cmd_alpha_ncd(argc, argv);
    }
    if (info_cstr_eq(argv[1], "eval-mdl-group") && argc >= 3) {
        return info_cmd_eval_mdl_group(argc, argv);
    }
    if (info_cstr_eq(argv[1], "causal-mdl") && argc >= 4) {
        return info_cmd_causal_mdl(argc, argv);
    }
    if (info_cstr_eq(argv[1], "classify-ctw")) {
        return info_cmd_classify_ctw(info_parse_opt(argc, argv, 2, "--out-json"));
    }
    if (info_cstr_eq(argv[1], "classify-separation")) {
        return info_cmd_classify_separation(info_parse_opt(argc, argv, 2, "--out-json"));
    }
    if (info_cstr_eq(argv[1], "classify-delsarte")) {
        return info_cmd_classify_delsarte(info_parse_opt(argc, argv, 2, "--out-json"));
    }
    if (info_cstr_eq(argv[1], "classify-causal")) {
        return info_cmd_classify_causal(info_parse_opt(argc, argv, 2, "--out-json"));
    }
    if (info_cstr_eq(argv[1], "hunt") && argc >= 3) {
        return info_cmd_hunt(argc, argv);
    }
    (void)fprintf(stderr, "ERROR: invalid arguments\n");
    return 1;
}
