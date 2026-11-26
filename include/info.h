#ifndef INFO_H
#define INFO_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "info_schema_abi.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ============================================================================
 * INFO v1.0.0 — Pure Algorithmic Information, Hutter Context-Mixing & Causal MDL
 * ============================================================================
 * Freestanding Ring-0 Pure-GPR C17 API (0 heap, 0 FPU/SIMD, 0 udiv/sdiv, 0 blr).
 * ============================================================================ */

#define INFO_INF1_MAGIC        UINT32_C(0x31464E49) /* "INF1" LE */
#define INFO_INF1_HEADER_BYTES UINT32_C(16)
#define INFO_CODEC_FLAG_ALG    UINT32_C(1)
#define INFO_LANG_RAW          UINT32_C(0)
#define INFO_LANG_C            UINT32_C(1)
#define INFO_LANG_LEAN         UINT32_C(2)
#define INFO_LANG_PY           UINT32_C(3)
#define INFO_LANG_LEAN_EXPR    UINT32_C(4)
#define INFO_LANG_C_STRICT     UINT32_C(5)
#define INFO_ALPHA_HT_SIZE     UINT32_C(8192)
#define INFO_ALPHA_MAX_IDS     UINT32_C(4096)
#define INFO_FNV1A_OFFSET      UINT64_C(0xCBF29CE484222325)
#define INFO_FNV1A_PRIME       UINT64_C(0x00000100000001B3)

#define INFO_WS_ORD2_SIZE      UINT32_C(262144)
#define INFO_WS_ORD3_SIZE      UINT32_C(524288)
#define INFO_WS_ORD4_SIZE      UINT32_C(524288)
#define INFO_WS_ORD6_SIZE      UINT32_C(524288)
#define INFO_WS_SPARSE_SIZE    UINT32_C(262144)
#define INFO_WS_WORD_SIZE      UINT32_C(524288)
#define INFO_WS_RING_SIZE      UINT32_C(1048576)
#define INFO_WS_MATCH_HT_SIZE  UINT32_C(262144)
#define INFO_WS_MIX_CTX        UINT32_C(512)
#define INFO_WS_NUM_EXPERTS    UINT32_C(10)
#define INFO_SSE_CTX           UINT32_C(256)
#define INFO_SSE_BINS          UINT32_C(33)

typedef struct {
    uint16_t ord0[256];
    uint16_t ord1[65536];
    uint32_t ord2[INFO_WS_ORD2_SIZE];
    uint32_t ord3[INFO_WS_ORD3_SIZE];
    uint32_t ord4[INFO_WS_ORD4_SIZE];
    uint32_t ord6[INFO_WS_ORD6_SIZE];
    uint32_t sparse[INFO_WS_SPARSE_SIZE];
    uint32_t word_tbl[INFO_WS_WORD_SIZE];
    uint8_t ring[INFO_WS_RING_SIZE];
    uint32_t match_ht[INFO_WS_MATCH_HT_SIZE];
    int32_t mix_w[INFO_WS_MIX_CTX][INFO_WS_NUM_EXPERTS];
    uint16_t sse[INFO_SSE_CTX][INFO_SSE_BINS];
} info_codec_ws_t;

typedef struct {
    uint64_t orig_bytes;
    uint64_t total_bits_q12;
    uint64_t alg_hits;
    uint64_t match_hits;
    uint64_t max_surprise_q12;
    uint64_t spike_offset;
    uint64_t f0_bits_q12;
    uint64_t f1_bits_q12;
    uint64_t payload_fnv;
} info_stream_eval_t;

typedef struct {
    uint64_t keys[INFO_ALPHA_HT_SIZE];
    uint16_t vals[INFO_ALPHA_HT_SIZE];
    uint32_t unique_ids;
    uint32_t vx_count;
} info_alpha_ws_t;

typedef struct {
    uint32_t count;
    uint64_t sum_indep_bits_q12;
    uint64_t seq_joint_bits_q12;
    uint64_t shared_bits_q12;
    uint64_t sum_cond_shared_bits_q12;
    int64_t joint_savings_bits_q12;
    int64_t extract_gain_bits_q12;
} info_joint_mdl_t;

typedef struct {
    uint64_t stationary_bytes;
    uint64_t kt_stat_bits_q12;
    uint64_t ctw_stat_bits_q12;
    uint64_t sw_ctw_stat_bits_q12;
    uint64_t switching_bytes;
    uint64_t kt_sw_bits_q12;
    uint64_t ctw_sw_bits_q12;
    uint64_t sw_ctw_sw_bits_q12;
    uint32_t kt_conservation_ok;
    uint32_t switching_dominates_ok;
} info_ctw_atlas_t;

typedef struct {
    uint64_t stream_bytes;
    uint64_t lfsr_ctx_bits;
    uint64_t lfsr_alg_bits;
    uint64_t lfsr_hits;
    uint32_t lfsr_roundtrip_ok;
    uint64_t ca_ctx_bits;
    uint64_t ca_alg_bits;
    uint64_t ca_hits;
    uint32_t ca_roundtrip_ok;
    uint64_t aff_ctx_bits;
    uint64_t aff_alg_bits;
    uint64_t aff_hits;
    uint32_t aff_roundtrip_ok;
} info_sep_atlas_t;

typedef struct {
    uint32_t n;
    uint32_t d;
    uint64_t searu_code_size;
    uint64_t singleton_ub;
    uint64_t hamming_ub;
    uint64_t plotkin_ub;
    uint64_t delsarte_ub_num;
    uint64_t delsarte_ub_den;
    uint32_t dual_verified;
    uint32_t tight;
} info_delsarte_row_t;

typedef struct {
    uint32_t num_rows;
    uint32_t all_dual_ok;
    info_delsarte_row_t rows[12];
} info_delsarte_atlas_t;

typedef struct {
    int64_t bp_low_num;
    int64_t bp_high_num;
    uint64_t bp_den;
    int64_t bp_true_num;
    uint32_t bp_sound;
    uint32_t obs_equiv_verified;
    uint32_t causal_mdl_pairs_tested;
    uint32_t causal_mdl_correct;
    uint32_t sym_joint_blind_count;
} info_causal_atlas_t;

typedef struct {
    uint64_t seed;
    uint64_t stream_bytes;
    uint64_t pure_ctx_bytes;
    uint64_t full_alg_bytes;
    uint64_t alg_hits;
    uint32_t law_kind;
    uint32_t lfsr_taps;
    uint16_t init_state;
    uint32_t roundtrip_ok;
    uint64_t merkle;
} info_hunt_alg_t;

typedef struct {
    uint64_t seed;
    uint64_t len;
    uint64_t switch_pos;
    uint64_t ctw_bits_q12;
    uint64_t sw_bits_q12;
    uint64_t reg_diff_q12;
    uint32_t sw_dominates;
    uint64_t merkle;
} info_hunt_ctw_t;

typedef struct {
    uint64_t seed;
    uint32_t n;
    uint32_t d;
    uint64_t searu_size;
    uint64_t delsarte_num;
    uint64_t delsarte_den;
    uint64_t hamming_ub;
    uint32_t dual_ok;
    uint64_t merkle;
    uint32_t codewords[32];
    int64_t dual_y[16];
} info_hunt_delsarte_t;

typedef struct {
    uint64_t seed;
    uint32_t counts_z0[4]; /* (x0,y0),(x0,y1),(x1,y0),(x1,y1) */
    uint32_t counts_z1[4];
    int64_t low_num;
    int64_t high_num;
    uint64_t den;
    int64_t true_num;
    uint32_t natural_bound_ok;
    uint32_t obs_equiv_ok;
    uint64_t merkle;
} info_hunt_bp_t;

typedef struct {
    uint64_t seed;
    uint64_t stream_bytes;
    uint64_t lx_bits_q12;
    uint64_t ly_bits_q12;
    uint64_t ly_given_x_bits_q12;
    uint64_t lx_given_y_bits_q12;
    uint64_t lxy_total_q12;
    uint64_t lyx_total_q12;
    uint32_t dir_recovered;
    uint64_t merkle;
} info_hunt_causal_mdl_t;

/* Core Ring-0 utilities */
void info_zero_bytes(void *dst, size_t n);
uint64_t info_fnv1a(const uint8_t *data, size_t n);
uint64_t info_fnv1a_u64(uint64_t h, uint64_t x);

/* Pure-integer 12-bit probability <-> logit <-> Q12 entropy LUT transforms (0 udiv, 0 floats) */
int32_t info_stretch(uint32_t p);
uint32_t info_squash(int32_t x);
uint32_t info_neg_log2_q12(uint32_t p);

/* 32-bit E1/E2/E3 Binary Arithmetic Coder raw self-test primitive */
size_t info_ac_test_roundtrip(const uint8_t *src, size_t len, uint8_t *scratch_cmp, size_t cap_cmp,
                              uint8_t *scratch_dec);

/* Hutter Context-Mixing + Algorithmic Law-Induction Codec ("INF1") */
void info_ws_reset(info_codec_ws_t *ws);
size_t info_compress(info_codec_ws_t *ws, const uint8_t *src, size_t len, uint8_t *dst,
                     size_t dst_cap, uint32_t flags);
size_t info_decompress(info_codec_ws_t *ws, const uint8_t *src, size_t src_len, uint8_t *dst,
                       size_t dst_cap);

/* Online predictor evaluation with optional conditional priming buffer */
void info_eval_stream_bits(info_codec_ws_t *ws, const uint8_t *prefix, size_t prefix_len,
                           const uint8_t *src, size_t len, uint32_t flags, info_stream_eval_t *out);

/* Structural α-canonicalization & Joint MDL abstraction gain evaluator */
size_t info_alpha_canonicalize(info_alpha_ws_t *aws, const uint8_t *src, size_t src_len,
                               uint32_t lang, uint8_t *dst, size_t dst_cap);
void info_eval_joint_mdl(info_codec_ws_t *ws, const uint8_t *const *streams, const size_t *lens,
                         uint32_t count, const uint8_t *shared_buf, size_t shared_len,
                         uint32_t flags, info_joint_mdl_t *out);

/* Pure-Theory Deterministic Stream Generators (used by separation classify & tests) */
void info_gen_lfsr16_stream(uint16_t init_state, uint8_t *dst, size_t len);
void info_gen_lfsr23_stream(uint32_t init_state, uint8_t *dst, size_t len);
void info_gen_ca_rule30_stream(uint8_t init_row, uint8_t *dst, size_t len);
void info_gen_ca32_rule30_stream(uint32_t init_row, uint8_t *dst, size_t len);
void info_gen_affine_mod256_stream(uint8_t a, uint8_t c, uint8_t x0, uint8_t *dst, size_t len);
void info_gen_affine16_stream(uint16_t a, uint16_t c, uint16_t x0, uint8_t *dst, size_t len);

/* Exact Krawtchouk & Delsarte Dual Verifier (0 udiv) */
int64_t info_krawtchouk_int(uint32_t n, uint32_t k, uint32_t x);
bool info_verify_delsarte_dual(uint32_t n, uint32_t d, uint64_t claimed_num, uint64_t claimed_den,
                               const int64_t *y_pos);
void info_balke_pearl_bounds(const uint32_t c0[4], const uint32_t c1[4], int64_t *low_num,
                             int64_t *high_num, uint64_t *den);

/* Four Ring-0 Theory Classifiers */
void info_classify_ctw(info_ctw_atlas_t *out);
void info_classify_separation(info_codec_ws_t *ws, uint8_t *buf_a, uint8_t *buf_cmp,
                              uint8_t *buf_dec, size_t buf_cap, info_sep_atlas_t *out);
void info_classify_delsarte(info_delsarte_atlas_t *out);
void info_classify_causal(info_codec_ws_t *ws, uint8_t *scratch_x, uint8_t *scratch_y,
                          info_causal_atlas_t *out);

/* Five Deterministic Hunt Witnesses */
void info_hunt_alg_blindspot(uint64_t seed, info_codec_ws_t *ws, uint8_t *buf_raw, uint8_t *buf_cmp,
                             uint8_t *buf_dec, size_t cap, info_hunt_alg_t *out);
void info_hunt_ctw_switch(uint64_t seed, info_hunt_ctw_t *out);
void info_hunt_delsarte_gap(uint64_t seed, info_hunt_delsarte_t *out);
void info_hunt_balke_pearl(uint64_t seed, info_hunt_bp_t *out);
void info_hunt_causal_mdl(uint64_t seed, info_codec_ws_t *ws, uint8_t *bx, uint8_t *by,
                          info_hunt_causal_mdl_t *out);

#ifdef __cplusplus
}
#endif

#endif /* INFO_H */
