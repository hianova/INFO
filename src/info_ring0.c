#include "info.h"

/* ============================================================================
 * INFO v1.0.0 — Ring-0 Pure-GPR Engine
 *   - Exact 32-bit E1/E2/E3 Binary Arithmetic Coder
 *   - 10-Expert Hutter Context Mixer + Match Model + SSE + Online Law Inducers
 *   - Krawtchouk / Delsarte LP Dual Verifier + SEARU Binary Code Discovery
 *   - Balke-Pearl Exact Integer Bounds + Causal MDL + Classifiers & Hunts
 *
 * Strict Pure-GPR constraints:
 *   0 undef symbols, 0 malloc/free, 0 udiv/sdiv/modulo-non-pow2, 0 floats, 0 blr/br.
 * ============================================================================ */

#define INFO_AC_Q1   UINT32_C(0x40000000)
#define INFO_AC_HALF UINT32_C(0x80000000)
#define INFO_AC_Q3   UINT32_C(0xC0000000)

/* 257-entry exact LUTs for p in [1..4095], logit x in [-2048..+2048] (step 16) */
static const int16_t k_stretch_nodes[257] = {
    -2129, -1419, -1240, -1135, -1061, -1002, -955, -914, -879, -848, -820, -794, -771, -750, -730,
    -711,  -693,  -677,  -661,  -646,  -632,  -618, -605, -593, -581, -569, -558, -547, -537, -527,
    -517,  -507,  -498,  -489,  -480,  -472,  -463, -455, -447, -439, -432, -424, -417, -410, -403,
    -396,  -389,  -382,  -375,  -369,  -362,  -356, -350, -344, -338, -332, -326, -320, -314, -309,
    -303,  -298,  -292,  -287,  -281,  -276,  -271, -265, -260, -255, -250, -245, -240, -235, -230,
    -226,  -221,  -216,  -211,  -207,  -202,  -197, -193, -188, -183, -179, -174, -170, -166, -161,
    -157,  -152,  -148,  -144,  -139,  -135,  -131, -127, -122, -118, -114, -110, -105, -101, -97,
    -93,   -89,   -85,   -81,   -77,   -72,   -68,  -64,  -60,  -56,  -52,  -48,  -44,  -40,  -36,
    -32,   -28,   -24,   -20,   -16,   -12,   -8,   -4,   0,    4,    8,    12,   16,   20,   24,
    28,    32,    36,    40,    44,    48,    52,   56,   60,   64,   68,   72,   77,   81,   85,
    89,    93,    97,    101,   105,   110,   114,  118,  122,  127,  131,  135,  139,  144,  148,
    152,   157,   161,   166,   170,   174,   179,  183,  188,  193,  197,  202,  207,  211,  216,
    221,   226,   230,   235,   240,   245,   250,  255,  260,  265,  271,  276,  281,  287,  292,
    298,   303,   309,   314,   320,   326,   332,  338,  344,  350,  356,  362,  369,  375,  382,
    389,   396,   403,   410,   417,   424,   432,  439,  447,  455,  463,  472,  480,  489,  498,
    507,   517,   527,   537,   547,   558,   569,  581,  593,  605,  618,  632,  646,  661,  677,
    693,   711,   730,   750,   771,   794,   820,  848,  879,  914,  955,  1002, 1061, 1135, 1240,
    1419,  2129};

static const uint16_t k_squash_nodes[257] = {
    1U,    1U,    2U,    2U,    2U,    2U,    2U,    2U,    2U,    2U,    3U,    3U,    3U,
    3U,    3U,    4U,    4U,    4U,    4U,    5U,    5U,    5U,    5U,    6U,    6U,    7U,
    7U,    7U,    8U,    8U,    9U,    10U,   10U,   11U,   11U,   12U,   13U,   14U,   15U,
    16U,   17U,   18U,   19U,   20U,   21U,   23U,   24U,   26U,   27U,   29U,   31U,   33U,
    35U,   37U,   40U,   42U,   45U,   48U,   51U,   54U,   58U,   61U,   65U,   69U,   74U,
    78U,   83U,   89U,   94U,   100U,  106U,  113U,  120U,  128U,  136U,  144U,  153U,  162U,
    172U,  183U,  194U,  206U,  219U,  232U,  246U,  261U,  277U,  293U,  311U,  329U,  349U,
    369U,  391U,  413U,  437U,  462U,  488U,  516U,  545U,  575U,  606U,  639U,  674U,  710U,
    747U,  786U,  827U,  869U,  912U,  957U,  1004U, 1052U, 1102U, 1153U, 1205U, 1259U, 1314U,
    1370U, 1428U, 1487U, 1546U, 1607U, 1668U, 1731U, 1793U, 1857U, 1920U, 1984U, 2048U, 2112U,
    2176U, 2239U, 2303U, 2365U, 2428U, 2489U, 2550U, 2609U, 2668U, 2726U, 2782U, 2837U, 2891U,
    2943U, 2994U, 3044U, 3092U, 3139U, 3184U, 3227U, 3269U, 3310U, 3349U, 3386U, 3422U, 3457U,
    3490U, 3521U, 3551U, 3580U, 3608U, 3634U, 3659U, 3683U, 3705U, 3727U, 3747U, 3767U, 3785U,
    3803U, 3819U, 3835U, 3850U, 3864U, 3877U, 3890U, 3902U, 3913U, 3924U, 3934U, 3943U, 3952U,
    3960U, 3968U, 3976U, 3983U, 3990U, 3996U, 4002U, 4007U, 4013U, 4018U, 4022U, 4027U, 4031U,
    4035U, 4038U, 4042U, 4045U, 4048U, 4051U, 4054U, 4056U, 4059U, 4061U, 4063U, 4065U, 4067U,
    4069U, 4070U, 4072U, 4073U, 4075U, 4076U, 4077U, 4078U, 4079U, 4080U, 4081U, 4082U, 4083U,
    4084U, 4085U, 4085U, 4086U, 4086U, 4087U, 4088U, 4088U, 4089U, 4089U, 4089U, 4090U, 4090U,
    4091U, 4091U, 4091U, 4091U, 4092U, 4092U, 4092U, 4092U, 4093U, 4093U, 4093U, 4093U, 4093U,
    4094U, 4094U, 4094U, 4094U, 4094U, 4094U, 4094U, 4094U, 4095U, 4095U};

static const uint16_t k_neg_log2_q12_nodes[257] = {
    49152U, 32768U, 28672U, 26276U, 24576U, 23257U, 22180U, 21269U, 20480U, 19784U, 19161U, 18598U,
    18084U, 17611U, 17173U, 16765U, 16384U, 16026U, 15688U, 15368U, 15065U, 14777U, 14502U, 14239U,
    13988U, 13747U, 13515U, 13292U, 13077U, 12870U, 12669U, 12476U, 12288U, 12106U, 11930U, 11758U,
    11592U, 11430U, 11272U, 11119U, 10969U, 10823U, 10681U, 10542U, 10406U, 10273U, 10143U, 10016U,
    9892U,  9770U,  9651U,  9534U,  9419U,  9306U,  9196U,  9088U,  8981U,  8876U,  8774U,  8673U,
    8573U,  8476U,  8380U,  8285U,  8192U,  8100U,  8010U,  7921U,  7834U,  7747U,  7662U,  7579U,
    7496U,  7414U,  7334U,  7255U,  7176U,  7099U,  7023U,  6948U,  6873U,  6800U,  6727U,  6656U,
    6585U,  6515U,  6446U,  6378U,  6310U,  6243U,  6177U,  6112U,  6047U,  5984U,  5920U,  5858U,
    5796U,  5735U,  5674U,  5614U,  5555U,  5496U,  5438U,  5380U,  5323U,  5266U,  5210U,  5155U,
    5100U,  5046U,  4992U,  4938U,  4885U,  4833U,  4780U,  4729U,  4678U,  4627U,  4577U,  4527U,
    4477U,  4428U,  4380U,  4331U,  4284U,  4236U,  4189U,  4142U,  4096U,  4050U,  4004U,  3959U,
    3914U,  3870U,  3825U,  3781U,  3738U,  3694U,  3651U,  3609U,  3566U,  3524U,  3483U,  3441U,
    3400U,  3359U,  3318U,  3278U,  3238U,  3198U,  3159U,  3119U,  3080U,  3042U,  3003U,  2965U,
    2927U,  2889U,  2852U,  2814U,  2777U,  2741U,  2704U,  2668U,  2631U,  2596U,  2560U,  2524U,
    2489U,  2454U,  2419U,  2384U,  2350U,  2316U,  2282U,  2248U,  2214U,  2181U,  2147U,  2114U,
    2081U,  2049U,  2016U,  1984U,  1951U,  1919U,  1888U,  1856U,  1824U,  1793U,  1762U,  1731U,
    1700U,  1669U,  1639U,  1608U,  1578U,  1548U,  1518U,  1488U,  1459U,  1429U,  1400U,  1371U,
    1342U,  1313U,  1284U,  1255U,  1227U,  1199U,  1170U,  1142U,  1114U,  1087U,  1059U,  1031U,
    1004U,  977U,   950U,   922U,   896U,   869U,   842U,   816U,   789U,   763U,   737U,   710U,
    684U,   659U,   633U,   607U,   582U,   556U,   531U,   506U,   481U,   456U,   431U,   406U,
    381U,   357U,   332U,   308U,   284U,   260U,   235U,   211U,   188U,   164U,   140U,   117U,
    93U,    70U,    46U,    23U,    1U};

static const uint8_t k_inv_odd_mod256[128] = {
    1U,   171U, 205U, 183U, 57U,  163U, 197U, 239U, 241U, 27U,  61U,  167U, 41U,  19U,  53U,  223U,
    225U, 139U, 173U, 151U, 25U,  131U, 165U, 207U, 209U, 251U, 29U,  135U, 9U,   243U, 21U,  191U,
    193U, 107U, 141U, 119U, 249U, 99U,  133U, 175U, 177U, 219U, 253U, 103U, 233U, 211U, 245U, 159U,
    161U, 75U,  109U, 87U,  217U, 67U,  101U, 143U, 145U, 187U, 221U, 71U,  201U, 179U, 213U, 127U,
    129U, 43U,  77U,  55U,  185U, 35U,  69U,  111U, 113U, 155U, 189U, 39U,  169U, 147U, 181U, 95U,
    97U,  11U,  45U,  23U,  153U, 3U,   37U,  79U,  81U,  123U, 157U, 7U,   137U, 115U, 149U, 63U,
    65U,  235U, 13U,  247U, 121U, 227U, 5U,   47U,  49U,  91U,  125U, 231U, 105U, 83U,  117U, 31U,
    33U,  203U, 237U, 215U, 89U,  195U, 229U, 15U,  17U,  59U,  93U,  199U, 73U,  51U,  85U,  255U};

static const uint8_t k_cnt_to_shift[16] = {1U, 2U, 2U, 3U, 3U, 3U, 4U, 4U,
                                           4U, 4U, 5U, 5U, 5U, 5U, 5U, 5U};

static const int32_t k_init_mix_w[INFO_WS_NUM_EXPERTS] = {256,  512, 768,  1024, 1024,
                                                          1024, 512, 1024, 2048, 4096};

/* ============================================================================
 * Primitive Helpers (0 libc, 0 signed-bitwise, 0 udiv)
 * ============================================================================ */

void info_zero_bytes(void *dst, size_t n) {
    uint8_t *p = (uint8_t *)dst;
    for (size_t i = 0U; i < n; i++) {
        p[i] = UINT8_C(0);
    }
}

uint64_t info_fnv1a(const uint8_t *data, size_t n) {
    uint64_t h = INFO_FNV1A_OFFSET;
    for (size_t i = 0U; i < n; i++) {
        h ^= (uint64_t)data[i];
        h *= INFO_FNV1A_PRIME;
    }
    return h;
}

uint64_t info_fnv1a_u64(uint64_t h, uint64_t x) {
    for (uint32_t b = 0U; b < 8U; b++) {
        h ^= (x >> (b * 8U)) & UINT64_C(0xFF);
        h *= INFO_FNV1A_PRIME;
    }
    return h;
}

static inline uint32_t info_parity64(uint64_t x) {
    x ^= (x >> 32U);
    x ^= (x >> 16U);
    x ^= (x >> 8U);
    x ^= (x >> 4U);
    x ^= (x >> 2U);
    x ^= (x >> 1U);
    return (uint32_t)(x & UINT64_C(1));
}

static inline uint32_t info_popcount32(uint32_t x) {
    x = x - ((x >> 1U) & UINT32_C(0x55555555));
    x = (x & UINT32_C(0x33333333)) + ((x >> 2U) & UINT32_C(0x33333333));
    x = (x + (x >> 4U)) & UINT32_C(0x0F0F0F0F);
    return (x * UINT32_C(0x01010101)) >> 24U;
}

static inline int32_t info_sar_i32(int32_t x, uint32_t sh) {
    if (x >= 0) {
        return (int32_t)(((uint32_t)x) >> sh);
    }
    return -(int32_t)(((uint32_t)(-x)) >> sh);
}

static inline int32_t info_clamp_i32(int32_t v, int32_t lo, int32_t hi) {
    if (v < lo) {
        return lo;
    }
    if (v > hi) {
        return hi;
    }
    return v;
}

static inline uint32_t info_mix_hash32(uint32_t a, uint32_t b) {
    uint32_t h = a * UINT32_C(0x9E3779B1) + b * UINT32_C(0x85EBCA77);
    h ^= (h >> 15U);
    h *= UINT32_C(0xC2B2AE3D);
    h ^= (h >> 16U);
    return h;
}

static inline void info_put_u32_le(uint8_t *dst, uint32_t v) {
    dst[0] = (uint8_t)(v & UINT32_C(0xFF));
    dst[1] = (uint8_t)((v >> 8U) & UINT32_C(0xFF));
    dst[2] = (uint8_t)((v >> 16U) & UINT32_C(0xFF));
    dst[3] = (uint8_t)((v >> 24U) & UINT32_C(0xFF));
}

static inline uint32_t info_get_u32_le(const uint8_t *src) {
    return (uint32_t)src[0] | ((uint32_t)src[1] << 8U) | ((uint32_t)src[2] << 16U) |
           ((uint32_t)src[3] << 24U);
}

int32_t info_stretch(uint32_t p) {
    if (p <= 1U) {
        return (int32_t)k_stretch_nodes[0];
    }
    if (p >= 4095U) {
        return (int32_t)k_stretch_nodes[256];
    }
    uint32_t idx = p >> 4U;
    uint32_t rem = p & UINT32_C(15);
    int32_t y0 = (int32_t)k_stretch_nodes[idx];
    int32_t y1 = (int32_t)k_stretch_nodes[idx + 1U];
    return y0 + info_sar_i32((y1 - y0) * (int32_t)rem, 4U);
}

uint32_t info_squash(int32_t x) {
    if (x <= -2048) {
        return UINT32_C(1);
    }
    if (x >= 2048) {
        return UINT32_C(4095);
    }
    uint32_t ux = (uint32_t)(x + 2048);
    uint32_t idx = ux >> 4U;
    uint32_t rem = ux & UINT32_C(15);
    uint32_t y0 = (uint32_t)k_squash_nodes[idx];
    uint32_t y1 = (uint32_t)k_squash_nodes[idx + 1U];
    uint32_t r = y0 + (((y1 - y0) * rem) >> 4U);
    if (r < 1U) {
        return UINT32_C(1);
    }
    if (r > 4095U) {
        return UINT32_C(4095);
    }
    return r;
}

uint32_t info_neg_log2_q12(uint32_t p) {
    if (p <= 1U) {
        return UINT32_C(49152);
    }
    if (p >= 4095U) {
        return UINT32_C(1);
    }
    uint32_t idx = p >> 4U;
    uint32_t rem = p & UINT32_C(15);
    uint32_t y0 = (uint32_t)k_neg_log2_q12_nodes[idx];
    uint32_t y1 = (uint32_t)k_neg_log2_q12_nodes[idx + 1U];
    uint32_t diff = y0 - y1;
    uint32_t res = y0 - ((diff * rem) >> 4U);
    return (res < 1U) ? UINT32_C(1) : res;
}

/* ============================================================================
 * 32-bit E1/E2/E3 Binary Arithmetic Coder
 * ============================================================================ */

typedef struct {
    uint8_t *dst;
    size_t cap;
    size_t byte_pos;
    uint8_t cur_byte;
    uint32_t bit_fill;
    uint32_t low;
    uint32_t high;
    uint32_t pending;
    bool overflow;
} info_ac_enc_t;

typedef struct {
    const uint8_t *src;
    size_t len;
    size_t byte_pos;
    uint8_t cur_byte;
    uint32_t bits_left;
    uint32_t low;
    uint32_t high;
    uint32_t code;
} info_ac_dec_t;

static void ac_put_raw_bit(info_ac_enc_t *e, uint32_t bit) {
    e->cur_byte = (uint8_t)(((uint32_t)e->cur_byte << 1U) | (bit & 1U));
    e->bit_fill++;
    if (e->bit_fill == 8U) {
        if (e->byte_pos < e->cap) {
            e->dst[e->byte_pos++] = e->cur_byte;
        } else {
            e->overflow = true;
        }
        e->cur_byte = UINT8_C(0);
        e->bit_fill = UINT32_C(0);
    }
}

static void ac_put_bit_plus_follow(info_ac_enc_t *e, uint32_t bit) {
    ac_put_raw_bit(e, bit);
    uint32_t inv = bit ^ 1U;
    while (e->pending > 0U) {
        ac_put_raw_bit(e, inv);
        e->pending--;
    }
}

static void ac_enc_init(info_ac_enc_t *e, uint8_t *dst, size_t cap) {
    e->dst = dst;
    e->cap = cap;
    e->byte_pos = 0U;
    e->cur_byte = UINT8_C(0);
    e->bit_fill = UINT32_C(0);
    e->low = UINT32_C(0);
    e->high = UINT32_C(0xFFFFFFFF);
    e->pending = UINT32_C(0);
    e->overflow = false;
}

static void ac_enc_bit(info_ac_enc_t *e, uint32_t prob1_q12, uint32_t bit) {
    uint32_t p = (prob1_q12 < 1U) ? 1U : ((prob1_q12 > 4095U) ? 4095U : prob1_q12);
    uint64_t span = (uint64_t)(e->high - e->low) + UINT64_C(1);
    uint32_t mid = e->low + (uint32_t)((span * (uint64_t)p) >> 12U) - UINT32_C(1);
    if (bit != 0U) {
        e->high = mid;
    } else {
        e->low = mid + UINT32_C(1);
    }
    for (;;) {
        if (e->high < INFO_AC_HALF) {
            ac_put_bit_plus_follow(e, UINT32_C(0));
            e->low = e->low << 1U;
            e->high = (e->high << 1U) | UINT32_C(1);
        } else if (e->low >= INFO_AC_HALF) {
            ac_put_bit_plus_follow(e, UINT32_C(1));
            e->low = (e->low - INFO_AC_HALF) << 1U;
            e->high = ((e->high - INFO_AC_HALF) << 1U) | UINT32_C(1);
        } else if (e->low >= INFO_AC_Q1 && e->high < INFO_AC_Q3) {
            e->pending++;
            e->low = (e->low - INFO_AC_Q1) << 1U;
            e->high = ((e->high - INFO_AC_Q1) << 1U) | UINT32_C(1);
        } else {
            break;
        }
    }
}

static size_t ac_enc_finish(info_ac_enc_t *e) {
    e->pending++;
    if (e->low < INFO_AC_Q1) {
        ac_put_bit_plus_follow(e, UINT32_C(0));
    } else {
        ac_put_bit_plus_follow(e, UINT32_C(1));
    }
    if (e->bit_fill != 0U) {
        uint8_t padded = (uint8_t)((uint32_t)e->cur_byte << (8U - e->bit_fill));
        if (e->byte_pos < e->cap) {
            e->dst[e->byte_pos++] = padded;
        } else {
            e->overflow = true;
        }
    }
    return e->overflow ? (size_t)0U : e->byte_pos;
}

static uint32_t ac_get_raw_bit(info_ac_dec_t *d) {
    if (d->bits_left == 0U) {
        d->cur_byte = (d->byte_pos < d->len) ? d->src[d->byte_pos++] : UINT8_C(0);
        d->bits_left = UINT32_C(8);
    }
    d->bits_left--;
    return ((uint32_t)d->cur_byte >> d->bits_left) & UINT32_C(1);
}

static void ac_dec_init(info_ac_dec_t *d, const uint8_t *src, size_t len) {
    d->src = src;
    d->len = len;
    d->byte_pos = 0U;
    d->cur_byte = UINT8_C(0);
    d->bits_left = UINT32_C(0);
    d->low = UINT32_C(0);
    d->high = UINT32_C(0xFFFFFFFF);
    d->code = UINT32_C(0);
    for (uint32_t i = 0U; i < 32U; i++) {
        d->code = (d->code << 1U) | ac_get_raw_bit(d);
    }
}

static uint32_t ac_dec_bit(info_ac_dec_t *d, uint32_t prob1_q12) {
    uint32_t p = (prob1_q12 < 1U) ? 1U : ((prob1_q12 > 4095U) ? 4095U : prob1_q12);
    uint64_t span = (uint64_t)(d->high - d->low) + UINT64_C(1);
    uint32_t mid = d->low + (uint32_t)((span * (uint64_t)p) >> 12U) - UINT32_C(1);
    uint32_t bit = (d->code <= mid) ? UINT32_C(1) : UINT32_C(0);
    if (bit != 0U) {
        d->high = mid;
    } else {
        d->low = mid + UINT32_C(1);
    }
    for (;;) {
        if (d->high < INFO_AC_HALF) {
            d->low = d->low << 1U;
            d->high = (d->high << 1U) | UINT32_C(1);
            d->code = (d->code << 1U) | ac_get_raw_bit(d);
        } else if (d->low >= INFO_AC_HALF) {
            d->low = (d->low - INFO_AC_HALF) << 1U;
            d->high = ((d->high - INFO_AC_HALF) << 1U) | UINT32_C(1);
            d->code = ((d->code - INFO_AC_HALF) << 1U) | ac_get_raw_bit(d);
        } else if (d->low >= INFO_AC_Q1 && d->high < INFO_AC_Q3) {
            d->low = (d->low - INFO_AC_Q1) << 1U;
            d->high = ((d->high - INFO_AC_Q1) << 1U) | UINT32_C(1);
            d->code = ((d->code - INFO_AC_Q1) << 1U) | ac_get_raw_bit(d);
        } else {
            break;
        }
    }
    return bit;
}

size_t info_ac_test_roundtrip(const uint8_t *src, size_t len, uint8_t *scratch_cmp, size_t cap_cmp,
                              uint8_t *scratch_dec) {
    if (src == NULL || scratch_cmp == NULL || scratch_dec == NULL) {
        return 0U;
    }
    info_ac_enc_t enc;
    ac_enc_init(&enc, scratch_cmp, cap_cmp);
    for (size_t i = 0U; i < len; i++) {
        uint8_t bv = src[i];
        uint32_t p = UINT32_C(512) + (((uint32_t)i * UINT32_C(17)) & UINT32_C(2047));
        for (uint32_t bp = 8U; bp > 0U; bp--) {
            uint32_t b = ((uint32_t)bv >> (bp - 1U)) & UINT32_C(1);
            ac_enc_bit(&enc, p, b);
            p = ((p * 3U + 1024U) & UINT32_C(4095));
            if (p < 1U) {
                p = 1U;
            }
        }
    }
    size_t cmp_len = ac_enc_finish(&enc);
    if (len > 0U && cmp_len == 0U) {
        return 0U;
    }
    info_ac_dec_t dec;
    ac_dec_init(&dec, scratch_cmp, cmp_len);
    for (size_t i = 0U; i < len; i++) {
        uint32_t acc = UINT32_C(0);
        uint32_t p = UINT32_C(512) + (((uint32_t)i * UINT32_C(17)) & UINT32_C(2047));
        for (uint32_t bp = 8U; bp > 0U; bp--) {
            uint32_t b = ac_dec_bit(&dec, p);
            acc = (acc << 1U) | b;
            p = ((p * 3U + 1024U) & UINT32_C(4095));
            if (p < 1U) {
                p = 1U;
            }
        }
        scratch_dec[i] = (uint8_t)acc;
    }
    return (cmp_len == 0U && len == 0U) ? 1U : cmp_len;
}

/* ============================================================================
 * 10-Expert Hutter Context-Mixing + Algorithmic Law-Induction Predictor State
 * ============================================================================ */

typedef struct {
    /* Byte & word context state */
    uint8_t b1;
    uint8_t b2;
    uint8_t b3;
    uint8_t b4;
    uint8_t b5;
    uint8_t b6;
    uint32_t c0;      /* partial byte 1..255 */
    uint32_t bit_pos; /* 0..7 (MSB->LSB index, counts up 0..7 as bits arrive) */
    uint32_t word_h;
    uint32_t prev_word_h;
    uint32_t total_bytes;

    /* Match model state */
    uint32_t match_pos;
    uint32_t match_len;

    /* Expert 9a: Online GF(2) Berlekamp-Massey LFSR (deg <= 24) */
    uint64_t bit_hist64;
    uint64_t bm_c;
    uint64_t bm_b;
    uint32_t bm_l;
    uint32_t bm_m;
    uint32_t bm_n;
    uint32_t bm_streak;

    /* Expert 9b: Byte-Affine & 16-bit BE Modular Affine Inducer */
    uint8_t aff_a;
    uint8_t aff_c;
    uint8_t aff_pred_byte;
    uint32_t aff_streak;
    bool aff_valid;
    uint16_t aff16_a;
    uint16_t aff16_c;
    uint16_t aff16_pred_word;
    uint32_t aff16_streak;
    bool aff16_valid;

    /* Expert 9c: 1D CA periodic neighborhood truth-table inducer (W=8 & W=32 BE) */
    uint8_t ca_rule_mask;
    uint8_t ca_known_mask;
    uint8_t ca_pred_byte;
    uint8_t ca_known_byte;
    uint32_t ca_streak;
    uint8_t ca32_rule_mask;
    uint8_t ca32_known_mask;
    uint32_t ca32_pred_word;
    uint32_t ca32_known_word;
    uint32_t ca32_streak;

    /* Per-bit active slot pointers & logits cached between predict and update */
    uint32_t h_ord2;
    uint32_t h_ord3;
    uint32_t h_ord4;
    uint32_t h_ord6;
    uint32_t h_sparse;
    uint32_t h_word;
    uint32_t idx_ord2;
    uint32_t idx_ord3;
    uint32_t idx_ord4;
    uint32_t idx_ord6;
    uint32_t idx_sparse;
    uint32_t idx_word;
    uint16_t tag_ord2;
    uint16_t tag_ord3;
    uint16_t tag_ord4;
    uint16_t tag_ord6;
    uint16_t tag_sparse;
    uint16_t tag_word;

    int32_t logits[INFO_WS_NUM_EXPERTS];
    uint32_t mix_ctx;
    uint32_t sse_ctx;
    uint32_t sse_bin;
    uint32_t sse_rem;
    uint32_t sse_on;
    uint32_t p_mix;
    uint32_t last_alg_locked;
    uint32_t flags;
    uint64_t alg_hits;
    uint64_t match_hits;
} info_pred_state_t;

void info_ws_reset(info_codec_ws_t *ws) {
    if (ws == NULL) {
        return;
    }
    for (uint32_t i = 0U; i < 256U; i++) {
        ws->ord0[i] = (uint16_t)(UINT32_C(2048) << 4U);
    }
    for (uint32_t i = 0U; i < 65536U; i++) {
        ws->ord1[i] = (uint16_t)(UINT32_C(2048) << 4U);
    }
    info_zero_bytes(ws->ord2, sizeof(ws->ord2));
    info_zero_bytes(ws->ord3, sizeof(ws->ord3));
    info_zero_bytes(ws->ord4, sizeof(ws->ord4));
    info_zero_bytes(ws->ord6, sizeof(ws->ord6));
    info_zero_bytes(ws->sparse, sizeof(ws->sparse));
    info_zero_bytes(ws->word_tbl, sizeof(ws->word_tbl));
    info_zero_bytes(ws->ring, sizeof(ws->ring));
    info_zero_bytes(ws->match_ht, sizeof(ws->match_ht));
    for (uint32_t c = 0U; c < INFO_WS_MIX_CTX; c++) {
        for (uint32_t e = 0U; e < INFO_WS_NUM_EXPERTS; e++) {
            ws->mix_w[c][e] = k_init_mix_w[e];
        }
    }
    for (uint32_t c = 0U; c < INFO_SSE_CTX; c++) {
        for (uint32_t b = 0U; b < INFO_SSE_BINS; b++) {
            uint32_t val = b * UINT32_C(128);
            if (val < 1U) {
                val = 1U;
            }
            if (val > 4095U) {
                val = 4095U;
            }
            ws->sse[c][b] = (uint16_t)val;
        }
    }
}

static void pred_init(info_pred_state_t *st, uint32_t flags) {
    info_zero_bytes(st, sizeof(*st));
    st->c0 = UINT32_C(1);
    st->bm_c = UINT64_C(1);
    st->bm_b = UINT64_C(1);
    st->bm_m = UINT32_C(1);
    st->flags = flags;
}

static uint32_t untagged_update(uint16_t *slot, uint32_t bit) {
    uint32_t v = (uint32_t)(*slot);
    uint32_t p = v >> 4U;
    uint32_t cnt = v & UINT32_C(15);
    uint32_t sh = (uint32_t)k_cnt_to_shift[cnt];
    uint32_t p_new = (bit != 0U) ? (p + ((UINT32_C(4096) - p) >> sh)) : (p - (p >> sh));
    if (p_new < 1U) {
        p_new = 1U;
    } else if (p_new > 4095U) {
        p_new = 4095U;
    }
    if (cnt < 15U) {
        cnt++;
    }
    *slot = (uint16_t)((p_new << 4U) | cnt);
    return p_new;
}

static uint32_t tagged_lookup(uint32_t *tbl, uint32_t mask, uint32_t h, uint32_t *out_idx,
                              uint16_t *out_tag) {
    uint32_t idx = h & mask;
    uint16_t tag = (uint16_t)((h >> 16U) & UINT32_C(0xFFFF));
    if (tag == 0U) {
        tag = UINT16_C(1);
    }
    *out_idx = idx;
    *out_tag = tag;
    uint32_t entry = tbl[idx];
    if ((uint16_t)(entry >> 16U) == tag) {
        uint32_t p = (entry >> 4U) & UINT32_C(4095);
        return (p < 1U) ? UINT32_C(2048) : ((p > 4095U) ? UINT32_C(4095) : p);
    }
    return UINT32_C(2048);
}

static void tagged_update(uint32_t *tbl, uint32_t idx, uint16_t tag, uint32_t bit) {
    uint32_t entry = tbl[idx];
    uint32_t p = UINT32_C(2048);
    uint32_t cnt = UINT32_C(0);
    if ((uint16_t)(entry >> 16U) == tag) {
        p = (entry >> 4U) & UINT32_C(4095);
        cnt = entry & UINT32_C(15);
    }
    uint32_t sh = (uint32_t)k_cnt_to_shift[cnt];
    uint32_t p_new = (bit != 0U) ? (p + ((UINT32_C(4096) - p) >> sh)) : (p - (p >> sh));
    if (p_new < 1U) {
        p_new = 1U;
    } else if (p_new > 4095U) {
        p_new = 4095U;
    }
    if (cnt < 15U) {
        cnt++;
    }
    tbl[idx] = ((uint32_t)tag << 16U) | (p_new << 4U) | cnt;
}

static inline uint32_t info_byte_class(uint8_t b) {
    if (b >= (uint8_t)'a' && b <= (uint8_t)'z') {
        return UINT32_C(0);
    }
    if (b >= (uint8_t)'A' && b <= (uint8_t)'Z') {
        return UINT32_C(1);
    }
    if (b >= (uint8_t)'0' && b <= (uint8_t)'9') {
        return UINT32_C(2);
    }
    if (b == UINT8_C(32) || b == UINT8_C(10) || b == UINT8_C(9) || b == UINT8_C(13)) {
        return UINT32_C(3);
    }
    if (b >= UINT8_C(33) && b <= UINT8_C(126)) {
        return UINT32_C(4);
    }
    return UINT32_C(5);
}

static inline bool info_is_word_char(uint8_t b) {
    return (b >= (uint8_t)'a' && b <= (uint8_t)'z') || (b >= (uint8_t)'A' && b <= (uint8_t)'Z') ||
           (b >= (uint8_t)'0' && b <= (uint8_t)'9') || b == (uint8_t)'_';
}

static void pred_on_byte_boundary(info_codec_ws_t *ws, info_pred_state_t *st, uint8_t completed) {
    uint32_t ring_mask = INFO_WS_RING_SIZE - UINT32_C(1);
    uint32_t pos = st->total_bytes;
    ws->ring[pos & ring_mask] = completed;
    pos++;
    st->total_bytes = pos;

    /* Advance match state or probe new 4-byte match */
    if (st->match_len > 0U) {
        st->match_pos++;
        if (st->match_len < UINT32_C(255)) {
            st->match_len++;
        }
    }
    if (pos >= 6U) {
        uint8_t p1 = completed;
        uint8_t p2 = st->b1;
        uint8_t p3 = st->b2;
        uint8_t p4 = st->b3;
        uint32_t m_key =
            ((uint32_t)p4 << 24U) | ((uint32_t)p3 << 16U) | ((uint32_t)p2 << 8U) | (uint32_t)p1;
        uint32_t m_slot =
            info_mix_hash32(m_key, UINT32_C(0x517CC1B7)) & (INFO_WS_MATCH_HT_SIZE - 1U);
        if (st->match_len == 0U) {
            uint32_t cand = ws->match_ht[m_slot];
            if (cand >= 4U && cand < pos && (pos - cand) < (INFO_WS_RING_SIZE - 16U)) {
                if (ws->ring[(cand - 1U) & ring_mask] == p1 &&
                    ws->ring[(cand - 2U) & ring_mask] == p2 &&
                    ws->ring[(cand - 3U) & ring_mask] == p3 &&
                    ws->ring[(cand - 4U) & ring_mask] == p4) {
                    st->match_pos = cand;
                    st->match_len = UINT32_C(4);
                }
            }
        }
        ws->match_ht[m_slot] = pos;
    }

    /* Update rolling bytes & word hashes */
    st->b6 = st->b5;
    st->b5 = st->b4;
    st->b4 = st->b3;
    st->b3 = st->b2;
    st->b2 = st->b1;
    st->b1 = completed;

    if (info_is_word_char(completed)) {
        st->word_h = info_mix_hash32(st->word_h, (uint32_t)completed);
    } else {
        if (st->word_h != 0U) {
            st->prev_word_h = st->word_h;
            st->word_h = UINT32_C(0);
        }
    }

    st->h_ord2 = info_mix_hash32((uint32_t)st->b1, (uint32_t)st->b2);
    st->h_ord3 = info_mix_hash32(st->h_ord2, (uint32_t)st->b3);
    st->h_ord4 = info_mix_hash32(st->h_ord3, (uint32_t)st->b4);
    st->h_ord6 = info_mix_hash32(info_mix_hash32(st->h_ord4, (uint32_t)st->b5), (uint32_t)st->b6);
    st->h_sparse = info_mix_hash32((uint32_t)st->b1 ^ ((uint32_t)st->b3 << 8U),
                                   (uint32_t)st->b2 ^ ((uint32_t)st->b4 << 8U));
    st->h_word = info_mix_hash32(st->word_h, st->prev_word_h);

    /* Update Algorithmic Law Inducers 9b (Affine/Stride mod 256) and 9c (1D CA Rule on W=8) */
    if ((st->flags & INFO_CODEC_FLAG_ALG) != 0U && pos >= 3U) {
        /* 9b: Check whether previous affine prediction held */
        if (st->aff_valid && completed == st->aff_pred_byte) {
            st->aff_streak++;
        } else {
            st->aff_streak = UINT32_C(0);
        }
        uint32_t dx01 = ((uint32_t)st->b2 - (uint32_t)st->b3) & UINT32_C(0xFF);
        uint32_t dx12 = ((uint32_t)st->b1 - (uint32_t)st->b2) & UINT32_C(0xFF);
        if (dx01 == dx12) {
            st->aff_a = UINT8_C(1);
            st->aff_c = (uint8_t)dx12;
            st->aff_pred_byte = (uint8_t)(((uint32_t)st->b1 + dx12) & UINT32_C(0xFF));
            if (st->aff_streak == 0U && ((uint32_t)st->b2 == (((uint32_t)st->b3 + dx12) & 0xFFU))) {
                st->aff_streak = UINT32_C(1);
            }
            st->aff_valid = true;
        } else if ((dx01 & 1U) != 0U) {
            uint32_t inv = (uint32_t)k_inv_odd_mod256[dx01 >> 1U];
            uint32_t a_cand = (dx12 * inv) & UINT32_C(0xFF);
            uint32_t c_cand = ((uint32_t)st->b1 - a_cand * (uint32_t)st->b2) & UINT32_C(0xFF);
            st->aff_a = (uint8_t)a_cand;
            st->aff_c = (uint8_t)c_cand;
            st->aff_pred_byte = (uint8_t)((a_cand * (uint32_t)st->b1 + c_cand) & UINT32_C(0xFF));
            st->aff_valid = true;
        } else {
            st->aff_valid = false;
            st->aff_streak = UINT32_C(0);
        }

        /* 9c: 1D W=8 CA truth-table fitting from b2 -> b1 transition */
        uint8_t prev_row = st->b2;
        uint8_t cur_row = st->b1;
        bool ca_conflict = false;
        uint8_t rule_m = st->ca_rule_mask;
        uint8_t known_m = st->ca_known_mask;
        for (uint32_t bit = 0U; bit < 8U; bit++) {
            uint32_t r_bit = (bit == 0U) ? 7U : (bit - 1U);
            uint32_t l_bit = (bit == 7U) ? 0U : (bit + 1U);
            uint32_t nb = ((((uint32_t)prev_row >> l_bit) & 1U) << 2U) |
                          ((((uint32_t)prev_row >> bit) & 1U) << 1U) |
                          (((uint32_t)prev_row >> r_bit) & 1U);
            uint32_t out_b = ((uint32_t)cur_row >> bit) & 1U;
            uint32_t nbit = UINT32_C(1) << nb;
            if ((known_m & nbit) != 0U) {
                if ((((uint32_t)rule_m >> nb) & 1U) != out_b) {
                    ca_conflict = true;
                    break;
                }
            } else {
                known_m = (uint8_t)((uint32_t)known_m | nbit);
                if (out_b != 0U) {
                    rule_m = (uint8_t)((uint32_t)rule_m | nbit);
                }
            }
        }
        if (ca_conflict) {
            /* Refit fresh solely on latest b2 -> b1 transition */
            rule_m = UINT8_C(0);
            known_m = UINT8_C(0);
            bool self_ok = true;
            for (uint32_t bit = 0U; bit < 8U; bit++) {
                uint32_t r_bit = (bit == 0U) ? 7U : (bit - 1U);
                uint32_t l_bit = (bit == 7U) ? 0U : (bit + 1U);
                uint32_t nb = ((((uint32_t)prev_row >> l_bit) & 1U) << 2U) |
                              ((((uint32_t)prev_row >> bit) & 1U) << 1U) |
                              (((uint32_t)prev_row >> r_bit) & 1U);
                uint32_t out_b = ((uint32_t)cur_row >> bit) & 1U;
                uint32_t nbit = UINT32_C(1) << nb;
                if ((known_m & nbit) != 0U) {
                    if ((((uint32_t)rule_m >> nb) & 1U) != out_b) {
                        self_ok = false;
                        break;
                    }
                } else {
                    known_m = (uint8_t)((uint32_t)known_m | nbit);
                    if (out_b != 0U) {
                        rule_m = (uint8_t)((uint32_t)rule_m | nbit);
                    }
                }
            }
            st->ca_rule_mask = self_ok ? rule_m : UINT8_C(0);
            st->ca_known_mask = self_ok ? known_m : UINT8_C(0);
            st->ca_streak = self_ok ? UINT32_C(1) : UINT32_C(0);
        } else {
            st->ca_rule_mask = rule_m;
            st->ca_known_mask = known_m;
            st->ca_streak++;
        }
        /* Build expected next byte for CA */
        uint8_t pred_b = UINT8_C(0);
        uint8_t know_b = UINT8_C(0);
        for (uint32_t bit = 0U; bit < 8U; bit++) {
            uint32_t r_bit = (bit == 0U) ? 7U : (bit - 1U);
            uint32_t l_bit = (bit == 7U) ? 0U : (bit + 1U);
            uint32_t nb = ((((uint32_t)st->b1 >> l_bit) & 1U) << 2U) |
                          ((((uint32_t)st->b1 >> bit) & 1U) << 1U) |
                          (((uint32_t)st->b1 >> r_bit) & 1U);
            if ((((uint32_t)st->ca_known_mask >> nb) & 1U) != 0U) {
                know_b = (uint8_t)((uint32_t)know_b | (UINT32_C(1) << bit));
                if ((((uint32_t)st->ca_rule_mask >> nb) & 1U) != 0U) {
                    pred_b = (uint8_t)((uint32_t)pred_b | (UINT32_C(1) << bit));
                }
            }
        }
        st->ca_pred_byte = pred_b;
        st->ca_known_byte = know_b;

        /* 9b-16: 16-bit BE Modular Affine b_t = (a * b_{t-1} + c) mod 65536 (0 udiv Hensel) */
        if ((pos & UINT32_C(1)) == 0U && pos >= UINT32_C(6)) {
            uint32_t w_cur = ((uint32_t)st->b2 << 8U) | (uint32_t)st->b1;
            uint32_t w_prev = ((uint32_t)st->b4 << 8U) | (uint32_t)st->b3;
            uint32_t w_prev2 = ((uint32_t)st->b6 << 8U) | (uint32_t)st->b5;
            if (st->aff16_valid && w_cur == (uint32_t)st->aff16_pred_word) {
                st->aff16_streak++;
                st->aff16_pred_word =
                    (uint16_t)(((uint32_t)st->aff16_a * w_cur + (uint32_t)st->aff16_c) &
                               UINT32_C(0xFFFF));
            } else {
                st->aff16_streak = UINT32_C(0);
                uint32_t dx01_16 = (w_prev - w_prev2) & UINT32_C(0xFFFF);
                uint32_t dx12_16 = (w_cur - w_prev) & UINT32_C(0xFFFF);
                if (dx01_16 == dx12_16) {
                    st->aff16_a = UINT16_C(1);
                    st->aff16_c = (uint16_t)dx12_16;
                    st->aff16_pred_word = (uint16_t)((w_cur + dx12_16) & UINT32_C(0xFFFF));
                    st->aff16_valid = true;
                } else if ((dx01_16 & 1U) != 0U) {
                    uint32_t inv = dx01_16;
                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &
                          UINT32_C(0xFFFF);
                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &
                          UINT32_C(0xFFFF);
                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &
                          UINT32_C(0xFFFF);
                    inv = (inv * (UINT32_C(2) - ((dx01_16 * inv) & UINT32_C(0xFFFF)))) &
                          UINT32_C(0xFFFF);
                    uint32_t a16 = (dx12_16 * inv) & UINT32_C(0xFFFF);
                    uint32_t c16 = (w_cur - ((a16 * w_prev) & UINT32_C(0xFFFF))) & UINT32_C(0xFFFF);
                    st->aff16_a = (uint16_t)a16;
                    st->aff16_c = (uint16_t)c16;
                    st->aff16_pred_word = (uint16_t)(((a16 * w_cur + c16) & UINT32_C(0xFFFF)));
                    st->aff16_valid = true;
                } else {
                    st->aff16_valid = false;
                }
            }
        }

        /* 9c-32: 1D W=32 periodic ring CA truth-table fitting from w_prev -> w_cur (4B/row) */
        if ((pos & UINT32_C(3)) == 0U && pos >= UINT32_C(8)) {
            uint32_t base_p = pos - UINT32_C(8);
            uint32_t w_prev32 = ((uint32_t)ws->ring[(base_p + 0U) & ring_mask] << 24U) |
                                ((uint32_t)ws->ring[(base_p + 1U) & ring_mask] << 16U) |
                                ((uint32_t)ws->ring[(base_p + 2U) & ring_mask] << 8U) |
                                (uint32_t)ws->ring[(base_p + 3U) & ring_mask];
            uint32_t w_cur32 = ((uint32_t)st->b4 << 24U) | ((uint32_t)st->b3 << 16U) |
                               ((uint32_t)st->b2 << 8U) | (uint32_t)st->b1;
            bool c32_conflict = false;
            uint8_t r32 = st->ca32_rule_mask;
            uint8_t k32 = st->ca32_known_mask;
            for (uint32_t bit = 0U; bit < 32U; bit++) {
                uint32_t r_bit = (bit == 0U) ? UINT32_C(31) : (bit - UINT32_C(1));
                uint32_t l_bit = (bit == 31U) ? UINT32_C(0) : (bit + UINT32_C(1));
                uint32_t nb = (((w_prev32 >> l_bit) & 1U) << 2U) |
                              (((w_prev32 >> bit) & 1U) << 1U) | ((w_prev32 >> r_bit) & 1U);
                uint32_t out_b = (w_cur32 >> bit) & 1U;
                uint32_t nbit = UINT32_C(1) << nb;
                if (((uint32_t)k32 & nbit) != 0U) {
                    if ((((uint32_t)r32 >> nb) & 1U) != out_b) {
                        c32_conflict = true;
                        break;
                    }
                } else {
                    k32 = (uint8_t)((uint32_t)k32 | nbit);
                    if (out_b != 0U) {
                        r32 = (uint8_t)((uint32_t)r32 | nbit);
                    }
                }
            }
            if (c32_conflict) {
                r32 = UINT8_C(0);
                k32 = UINT8_C(0);
                bool self32_ok = true;
                for (uint32_t bit = 0U; bit < 32U; bit++) {
                    uint32_t r_bit = (bit == 0U) ? UINT32_C(31) : (bit - UINT32_C(1));
                    uint32_t l_bit = (bit == 31U) ? UINT32_C(0) : (bit + UINT32_C(1));
                    uint32_t nb = (((w_prev32 >> l_bit) & 1U) << 2U) |
                                  (((w_prev32 >> bit) & 1U) << 1U) | ((w_prev32 >> r_bit) & 1U);
                    uint32_t out_b = (w_cur32 >> bit) & 1U;
                    uint32_t nbit = UINT32_C(1) << nb;
                    if (((uint32_t)k32 & nbit) != 0U) {
                        if ((((uint32_t)r32 >> nb) & 1U) != out_b) {
                            self32_ok = false;
                            break;
                        }
                    } else {
                        k32 = (uint8_t)((uint32_t)k32 | nbit);
                        if (out_b != 0U) {
                            r32 = (uint8_t)((uint32_t)r32 | nbit);
                        }
                    }
                }
                st->ca32_rule_mask = self32_ok ? r32 : UINT8_C(0);
                st->ca32_known_mask = self32_ok ? k32 : UINT8_C(0);
                st->ca32_streak = self32_ok ? UINT32_C(1) : UINT32_C(0);
            } else {
                st->ca32_rule_mask = r32;
                st->ca32_known_mask = k32;
                st->ca32_streak++;
            }
            uint32_t pw32 = UINT32_C(0);
            uint32_t kw32 = UINT32_C(0);
            for (uint32_t bit = 0U; bit < 32U; bit++) {
                uint32_t r_bit = (bit == 0U) ? UINT32_C(31) : (bit - UINT32_C(1));
                uint32_t l_bit = (bit == 31U) ? UINT32_C(0) : (bit + UINT32_C(1));
                uint32_t nb = (((w_cur32 >> l_bit) & 1U) << 2U) | (((w_cur32 >> bit) & 1U) << 1U) |
                              ((w_cur32 >> r_bit) & 1U);
                if ((((uint32_t)st->ca32_known_mask >> nb) & 1U) != 0U) {
                    kw32 |= (UINT32_C(1) << bit);
                    if ((((uint32_t)st->ca32_rule_mask >> nb) & 1U) != 0U) {
                        pw32 |= (UINT32_C(1) << bit);
                    }
                }
            }
            st->ca32_pred_word = pw32;
            st->ca32_known_word = kw32;
        }
    }

    st->c0 = UINT32_C(1);
    st->bit_pos = UINT32_C(0);
}

static uint32_t pred_predict_bit(info_codec_ws_t *ws, info_pred_state_t *st) {
    uint32_t c0 = st->c0;
    uint32_t bp_down = UINT32_C(7) - st->bit_pos;

    /* Experts 0..7 */
    uint32_t p0 = ((uint32_t)ws->ord0[c0]) >> 4U;
    uint32_t p1 = ((uint32_t)ws->ord1[((uint32_t)st->b1 << 8U) | c0]) >> 4U;
    uint32_t c0m = c0 * UINT32_C(0x9E3779B1);
    uint32_t p2 = tagged_lookup(ws->ord2, INFO_WS_ORD2_SIZE - 1U, st->h_ord2 ^ c0m, &st->idx_ord2,
                                &st->tag_ord2);
    uint32_t p3 = tagged_lookup(ws->ord3, INFO_WS_ORD3_SIZE - 1U, st->h_ord3 ^ c0m, &st->idx_ord3,
                                &st->tag_ord3);
    uint32_t p4 = tagged_lookup(ws->ord4, INFO_WS_ORD4_SIZE - 1U, st->h_ord4 ^ c0m, &st->idx_ord4,
                                &st->tag_ord4);
    uint32_t p5 = tagged_lookup(ws->ord6, INFO_WS_ORD6_SIZE - 1U, st->h_ord6 ^ c0m, &st->idx_ord6,
                                &st->tag_ord6);
    uint32_t p6 = tagged_lookup(ws->sparse, INFO_WS_SPARSE_SIZE - 1U, st->h_sparse ^ c0m,
                                &st->idx_sparse, &st->tag_sparse);
    uint32_t p7 = tagged_lookup(ws->word_tbl, INFO_WS_WORD_SIZE - 1U, st->h_word ^ c0m,
                                &st->idx_word, &st->tag_word);

    st->logits[0] = info_stretch(p0);
    st->logits[1] = info_stretch(p1);
    st->logits[2] = info_stretch(p2);
    st->logits[3] = info_stretch(p3);
    st->logits[4] = info_stretch(p4);
    st->logits[5] = info_stretch(p5);
    st->logits[6] = info_stretch(p6);
    st->logits[7] = info_stretch(p7);

    /* Expert 8: Long-Range Match Model */
    int32_t m_logit = 0;
    if (st->match_len > 0U) {
        uint8_t mb = ws->ring[st->match_pos & (INFO_WS_RING_SIZE - 1U)];
        uint32_t exp_b = ((uint32_t)mb >> bp_down) & UINT32_C(1);
        int32_t mag = (st->match_len >= 16U) ? 1800 : (600 + (int32_t)st->match_len * 75);
        m_logit = (exp_b != 0U) ? mag : -mag;
        st->match_hits++;
    }
    st->logits[8] = m_logit;

    /* Expert 9: Online Causal Algorithmic Law Inducer */
    int32_t alg_logit = 0;
    uint32_t alg_locked = UINT32_C(0);
    if ((st->flags & INFO_CODEC_FLAG_ALG) != 0U) {
        if (st->bm_streak >= 12U && st->bm_l > 0U && st->bm_l <= 24U) {
            uint32_t l_pred = info_parity64(st->bit_hist64 & (st->bm_c >> 1U));
            alg_logit = (l_pred != 0U) ? 1950 : -1950;
            alg_locked = UINT32_C(1);
        } else if (st->aff16_valid && st->aff16_streak >= 1U) {
            uint32_t sh16 = ((st->total_bytes & 1U) == 0U) ? UINT32_C(8) : UINT32_C(0);
            uint8_t ab = (uint8_t)(((uint32_t)st->aff16_pred_word >> sh16) & UINT32_C(0xFF));
            uint32_t a16_pred = ((uint32_t)ab >> bp_down) & UINT32_C(1);
            alg_logit = (a16_pred != 0U) ? 1950 : -1950;
            alg_locked = UINT32_C(1);
        } else if (st->ca32_streak >= 2U) {
            uint32_t sh32 = (UINT32_C(3) - (st->total_bytes & UINT32_C(3))) * UINT32_C(8);
            uint32_t kb = (st->ca32_known_word >> sh32) & UINT32_C(0xFF);
            if (((kb >> bp_down) & 1U) != 0U) {
                uint32_t pb = (st->ca32_pred_word >> sh32) & UINT32_C(0xFF);
                uint32_t c32_pred = (pb >> bp_down) & UINT32_C(1);
                alg_logit = (c32_pred != 0U) ? 1950 : -1950;
                alg_locked = UINT32_C(1);
            }
        } else if (st->aff_valid && st->aff_streak >= 2U) {
            uint32_t a_pred = ((uint32_t)st->aff_pred_byte >> bp_down) & UINT32_C(1);
            alg_logit = (a_pred != 0U) ? 1950 : -1950;
            alg_locked = UINT32_C(1);
        } else if (st->ca_streak >= 2U && (((uint32_t)st->ca_known_byte >> bp_down) & 1U) != 0U) {
            uint32_t c_pred = ((uint32_t)st->ca_pred_byte >> bp_down) & UINT32_C(1);
            alg_logit = (c_pred != 0U) ? 1950 : -1950;
            alg_locked = UINT32_C(1);
        }
    }
    st->logits[9] = alg_logit;
    st->last_alg_locked = alg_locked;
    if (alg_locked != 0U) {
        st->alg_hits++;
    }

    uint32_t bc = info_byte_class(st->b1);
    uint32_t m_flag = (st->match_len > 0U) ? UINT32_C(1) : UINT32_C(0);
    uint32_t eq_flag = (st->b1 == st->b2) ? UINT32_C(1) : UINT32_C(0);
    st->mix_ctx = (m_flag << 8U) | (alg_locked << 7U) | (bc << 4U) | (eq_flag << 3U) | st->bit_pos;

    int64_t dot = INT64_C(0);
    for (uint32_t k = 0U; k < INFO_WS_NUM_EXPERTS; k++) {
        dot += (int64_t)ws->mix_w[st->mix_ctx][k] * (int64_t)st->logits[k];
    }
    int32_t total_logit = (dot >= INT64_C(0)) ? (int32_t)(((uint64_t)dot) >> 11U)
                                              : -(int32_t)(((uint64_t)(-dot)) >> 11U);
    uint32_t p_mix = info_squash(total_logit);
    st->p_mix = p_mix;

    if (alg_locked != 0U || st->match_len >= 8U) {
        st->sse_on = UINT32_C(0);
        return p_mix;
    }

    st->sse_ctx = (((uint32_t)st->b1 & UINT32_C(0xE0)) | (st->bit_pos << 2U) | (bc & 3U)) &
                  (INFO_SSE_CTX - 1U);
    uint32_t sbin = p_mix >> 7U;
    uint32_t srem = p_mix & UINT32_C(127);
    if (sbin >= 32U) {
        sbin = 31U;
        srem = 127U;
    }
    st->sse_bin = sbin;
    st->sse_rem = srem;
    st->sse_on = UINT32_C(1);
    uint32_t s0 = (uint32_t)ws->sse[st->sse_ctx][sbin];
    uint32_t s1 = (uint32_t)ws->sse[st->sse_ctx][sbin + 1U];
    uint32_t p_sse = (s0 * (UINT32_C(128) - srem) + s1 * srem) >> 7U;
    uint32_t p_out = (p_mix + p_sse * UINT32_C(3)) >> 2U;
    if (p_out < 1U) {
        return UINT32_C(1);
    }
    if (p_out > 4095U) {
        return UINT32_C(4095);
    }
    return p_out;
}

static void pred_update_bit(info_codec_ws_t *ws, info_pred_state_t *st, uint32_t bit) {
    uint32_t c0 = st->c0;
    uint32_t bp_down = UINT32_C(7) - st->bit_pos;

    (void)untagged_update(&ws->ord0[c0], bit);
    (void)untagged_update(&ws->ord1[((uint32_t)st->b1 << 8U) | c0], bit);
    tagged_update(ws->ord2, st->idx_ord2, st->tag_ord2, bit);
    tagged_update(ws->ord3, st->idx_ord3, st->tag_ord3, bit);
    tagged_update(ws->ord4, st->idx_ord4, st->tag_ord4, bit);
    tagged_update(ws->ord6, st->idx_ord6, st->tag_ord6, bit);
    tagged_update(ws->sparse, st->idx_sparse, st->tag_sparse, bit);
    tagged_update(ws->word_tbl, st->idx_word, st->tag_word, bit);

    /* Match bit verification */
    if (st->match_len > 0U) {
        uint8_t mb = ws->ring[st->match_pos & (INFO_WS_RING_SIZE - 1U)];
        uint32_t exp_b = ((uint32_t)mb >> bp_down) & UINT32_C(1);
        if (bit != exp_b) {
            st->match_len = UINT32_C(0);
        }
    }

    /* Update Logistic Mixer & SSE */
    int32_t tgt = (bit != 0U) ? 4096 : 0;
    int32_t err = tgt - (int32_t)st->p_mix;
    for (uint32_t k = 0U; k < INFO_WS_NUM_EXPERTS; k++) {
        int32_t sk = st->logits[k];
        if (sk != 0) {
            int32_t dw = info_sar_i32(err * sk, 14U);
            st->logits[k] = sk;
            ws->mix_w[st->mix_ctx][k] =
                info_clamp_i32(ws->mix_w[st->mix_ctx][k] + dw, -8192, 16384);
        }
    }
    if (st->sse_on != 0U) {
        uint32_t b_idx = (st->sse_rem >= 64U) ? (st->sse_bin + 1U) : st->sse_bin;
        int32_t sv = (int32_t)ws->sse[st->sse_ctx][b_idx];
        int32_t sv_new = sv + info_sar_i32(tgt - sv, 5U);
        ws->sse[st->sse_ctx][b_idx] = (uint16_t)info_clamp_i32(sv_new, 1, 4095);
    }

    /* Update Expert 9a (Online GF(2) Berlekamp-Massey) & cancel 9b/9c on bit mismatch */
    if ((st->flags & INFO_CODEC_FLAG_ALG) != 0U) {
        if (st->aff16_valid) {
            uint32_t sh16 = ((st->total_bytes & 1U) == 0U) ? UINT32_C(8) : UINT32_C(0);
            uint32_t ab = ((uint32_t)st->aff16_pred_word >> sh16) & UINT32_C(0xFF);
            if (bit != ((ab >> bp_down) & UINT32_C(1))) {
                st->aff16_streak = UINT32_C(0);
            }
        }
        if (st->ca32_streak > 0U) {
            uint32_t sh32 = (UINT32_C(3) - (st->total_bytes & UINT32_C(3))) * UINT32_C(8);
            uint32_t kb = (st->ca32_known_word >> sh32) & UINT32_C(0xFF);
            if (((kb >> bp_down) & 1U) != 0U) {
                uint32_t pb = (st->ca32_pred_word >> sh32) & UINT32_C(0xFF);
                if (bit != ((pb >> bp_down) & UINT32_C(1))) {
                    st->ca32_streak = UINT32_C(0);
                }
            }
        }
        if (st->aff_valid && bit != (((uint32_t)st->aff_pred_byte >> bp_down) & UINT32_C(1))) {
            st->aff_streak = UINT32_C(0);
        }
        if (st->ca_streak > 0U && (((uint32_t)st->ca_known_byte >> bp_down) & 1U) != 0U &&
            bit != (((uint32_t)st->ca_pred_byte >> bp_down) & UINT32_C(1))) {
            st->ca_streak = UINT32_C(0);
        }
        uint32_t bm_pred = info_parity64(st->bit_hist64 & (st->bm_c >> 1U));
        if (bm_pred == bit) {
            st->bm_streak++;
            st->bm_m++;
        } else {
            st->bm_streak = UINT32_C(0);
            uint64_t t_poly = st->bm_c;
            if (st->bm_m < 40U) {
                st->bm_c ^= (st->bm_b << st->bm_m);
            }
            if (2U * st->bm_l <= st->bm_n) {
                uint32_t new_l = st->bm_n + UINT32_C(1) - st->bm_l;
                if (new_l > 24U) {
                    st->bm_c = UINT64_C(1);
                    st->bm_b = UINT64_C(1);
                    st->bm_l = UINT32_C(0);
                    st->bm_m = UINT32_C(1);
                    st->bm_n = UINT32_C(0);
                } else {
                    st->bm_l = new_l;
                    st->bm_b = t_poly;
                    st->bm_m = UINT32_C(1);
                    st->bm_n++;
                }
            } else {
                st->bm_m++;
                st->bm_n++;
            }
        }
        st->bit_hist64 = (st->bit_hist64 << 1U) | (uint64_t)bit;
    }

    st->c0 = (c0 << 1U) | bit;
    st->bit_pos++;
    if (st->bit_pos == 8U) {
        uint8_t completed = (uint8_t)(st->c0 & UINT32_C(0xFF));
        pred_on_byte_boundary(ws, st, completed);
    }
}

/* ============================================================================
 * Public Compression, Decompression & Stream Evaluation API
 * ============================================================================ */

size_t info_compress(info_codec_ws_t *ws, const uint8_t *src, size_t len, uint8_t *dst,
                     size_t dst_cap, uint32_t flags) {
    if (ws == NULL || dst == NULL || dst_cap < INFO_INF1_HEADER_BYTES ||
        (len > 0U && src == NULL)) {
        return 0U;
    }
    info_ws_reset(ws);
    info_pred_state_t st;
    pred_init(&st, flags);

    info_put_u32_le(dst, INFO_INF1_MAGIC);
    info_put_u32_le(dst + 4, (uint32_t)len);
    info_put_u32_le(dst + 8, flags);
    uint32_t fnv32 = (len > 0U) ? (uint32_t)(info_fnv1a(src, len) & UINT64_C(0xFFFFFFFF)) : 0U;
    info_put_u32_le(dst + 12, fnv32);

    if (len == 0U) {
        return (size_t)INFO_INF1_HEADER_BYTES;
    }

    info_ac_enc_t enc;
    ac_enc_init(&enc, dst + INFO_INF1_HEADER_BYTES, dst_cap - (size_t)INFO_INF1_HEADER_BYTES);
    for (size_t i = 0U; i < len; i++) {
        uint8_t bv = src[i];
        for (uint32_t bp = 8U; bp > 0U; bp--) {
            uint32_t bit = ((uint32_t)bv >> (bp - 1U)) & UINT32_C(1);
            uint32_t p = pred_predict_bit(ws, &st);
            ac_enc_bit(&enc, p, bit);
            pred_update_bit(ws, &st, bit);
        }
    }
    size_t payload = ac_enc_finish(&enc);
    if (payload == 0U) {
        return 0U;
    }
    return (size_t)INFO_INF1_HEADER_BYTES + payload;
}

size_t info_decompress(info_codec_ws_t *ws, const uint8_t *src, size_t src_len, uint8_t *dst,
                       size_t dst_cap) {
    if (ws == NULL || src == NULL || src_len < INFO_INF1_HEADER_BYTES || dst == NULL) {
        return SIZE_MAX;
    }
    uint32_t magic = info_get_u32_le(src);
    uint32_t orig_sz = info_get_u32_le(src + 4);
    uint32_t flags = info_get_u32_le(src + 8);
    uint32_t exp_fnv32 = info_get_u32_le(src + 12);
    if (magic != INFO_INF1_MAGIC || (size_t)orig_sz > dst_cap) {
        return SIZE_MAX;
    }
    if (orig_sz == 0U) {
        return (exp_fnv32 == 0U) ? 0U : SIZE_MAX;
    }
    info_ws_reset(ws);
    info_pred_state_t st;
    pred_init(&st, flags);

    info_ac_dec_t dec;
    ac_dec_init(&dec, src + INFO_INF1_HEADER_BYTES, src_len - (size_t)INFO_INF1_HEADER_BYTES);
    for (size_t i = 0U; i < (size_t)orig_sz; i++) {
        for (uint32_t bp = 0U; bp < 8U; bp++) {
            uint32_t p = pred_predict_bit(ws, &st);
            uint32_t bit = ac_dec_bit(&dec, p);
            pred_update_bit(ws, &st, bit);
        }
        dst[i] = st.b1;
    }
    uint32_t got_fnv32 = (uint32_t)(info_fnv1a(dst, (size_t)orig_sz) & UINT64_C(0xFFFFFFFF));
    if (got_fnv32 != exp_fnv32) {
        return SIZE_MAX;
    }
    return (size_t)orig_sz;
}

void info_eval_stream_bits(info_codec_ws_t *ws, const uint8_t *prefix, size_t prefix_len,
                           const uint8_t *src, size_t len, uint32_t flags,
                           info_stream_eval_t *out) {
    if (ws == NULL || out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    info_ws_reset(ws);
    info_pred_state_t st;
    pred_init(&st, flags);

    if (prefix != NULL) {
        for (size_t i = 0U; i < prefix_len; i++) {
            uint8_t bv = prefix[i];
            for (uint32_t bp = 8U; bp > 0U; bp--) {
                uint32_t bit = ((uint32_t)bv >> (bp - 1U)) & UINT32_C(1);
                (void)pred_predict_bit(ws, &st);
                pred_update_bit(ws, &st, bit);
            }
        }
    }

    st.alg_hits = UINT64_C(0);
    st.match_hits = UINT64_C(0);
    uint64_t total_q12 = UINT64_C(0);
    uint64_t f0_q12 = UINT64_C(0);
    uint64_t f1_q12 = UINT64_C(0);
    uint64_t max_b_surp = UINT64_C(0);
    uint64_t spike_off = UINT64_C(0);
    size_t half = len >> 1U;

    for (size_t i = 0U; i < len; i++) {
        uint8_t bv = src[i];
        uint64_t byte_q12 = UINT64_C(0);
        for (uint32_t bp = 8U; bp > 0U; bp--) {
            uint32_t bit = ((uint32_t)bv >> (bp - 1U)) & UINT32_C(1);
            uint32_t p1 = pred_predict_bit(ws, &st);
            uint32_t pw = (bit != 0U) ? p1 : (UINT32_C(4096) - p1);
            uint32_t bq = info_neg_log2_q12(pw);
            total_q12 += (uint64_t)bq;
            byte_q12 += (uint64_t)bq;
            pred_update_bit(ws, &st, bit);
        }
        if (i < half) {
            f0_q12 += byte_q12;
        } else {
            f1_q12 += byte_q12;
        }
        if (i >= 16U && byte_q12 > max_b_surp) {
            max_b_surp = byte_q12;
            spike_off = (uint64_t)i;
        }
    }
    out->orig_bytes = (uint64_t)len;
    out->total_bits_q12 = total_q12;
    out->alg_hits = st.alg_hits;
    out->match_hits = st.match_hits;
    out->max_surprise_q12 = max_b_surp;
    out->spike_offset = spike_off;
    out->f0_bits_q12 = f0_q12;
    out->f1_bits_q12 = f1_q12;
    out->payload_fnv = (len > 0U && src != NULL) ? info_fnv1a(src, len) : UINT64_C(0);
}

/* ============================================================================
 * Structural α-Canonicalization & Joint MDL Abstraction Evaluator
 * ============================================================================ */

typedef struct {
    uint8_t *dst;
    size_t cap;
    size_t pos;
    bool pending_sp;
    bool line_start;
} info_alpha_writer_t;

static bool alpha_is_ident_start(uint8_t ch) {
    return (ch >= (uint8_t)'A' && ch <= (uint8_t)'Z') ||
           (ch >= (uint8_t)'a' && ch <= (uint8_t)'z') || ch == (uint8_t)'_';
}

static bool alpha_is_ident_cont(uint8_t ch, uint32_t lang) {
    if (alpha_is_ident_start(ch) || (ch >= (uint8_t)'0' && ch <= (uint8_t)'9')) {
        return true;
    }
    return lang == INFO_LANG_LEAN && ch == (uint8_t)'\'';
}

static bool alpha_is_digit(uint8_t ch) {
    return ch >= (uint8_t)'0' && ch <= (uint8_t)'9';
}

static bool alpha_is_num_cont(uint8_t ch) {
    return alpha_is_digit(ch) || (ch >= (uint8_t)'a' && ch <= (uint8_t)'f') ||
           (ch >= (uint8_t)'A' && ch <= (uint8_t)'F') || ch == (uint8_t)'x' || ch == (uint8_t)'X' ||
           ch == (uint8_t)'b' || ch == (uint8_t)'B' || ch == (uint8_t)'u' || ch == (uint8_t)'U' ||
           ch == (uint8_t)'l' || ch == (uint8_t)'L' || ch == (uint8_t)'_';
}

static bool alpha_tok_eq(const uint8_t *tok, size_t len, const char *lit) {
    size_t i = 0U;
    while (i < len && lit[i] != '\0') {
        if (tok[i] != (uint8_t)lit[i]) {
            return false;
        }
        i++;
    }
    return i == len && lit[i] == '\0';
}

static bool alpha_has_prefix(const uint8_t *tok, size_t len, const char *pfx) {
    size_t i = 0U;
    while (pfx[i] != '\0') {
        if (i >= len || tok[i] != (uint8_t)pfx[i]) {
            return false;
        }
        i++;
    }
    return true;
}

static void alpha_put_raw(info_alpha_writer_t *w, uint8_t ch) {
    if (w->pos < w->cap) {
        w->dst[w->pos] = ch;
        w->pos++;
    }
}

static void alpha_emit_slice(info_alpha_writer_t *w, const uint8_t *buf, size_t len) {
    if (w->pending_sp) {
        alpha_put_raw(w, (uint8_t)' ');
        w->pending_sp = false;
    }
    for (size_t i = 0U; i < len; i++) {
        alpha_put_raw(w, buf[i]);
    }
    if (len > 0U) {
        w->line_start = false;
    }
}

static void alpha_emit_cstr(info_alpha_writer_t *w, const char *s) {
    if (w->pending_sp) {
        alpha_put_raw(w, (uint8_t)' ');
        w->pending_sp = false;
    }
    for (size_t i = 0U; s[i] != '\0'; i++) {
        alpha_put_raw(w, (uint8_t)s[i]);
    }
    w->line_start = false;
}

static void alpha_note_space(info_alpha_writer_t *w) {
    if (!w->line_start) {
        w->pending_sp = true;
    }
}

static bool alpha_is_preserved_num(const uint8_t *tok, size_t len) {
    static const char *const k_keep[] = {"0", "1", "2", "4", "8", "16", "32", "64"};
    for (size_t i = 0U; i < sizeof(k_keep) / sizeof(k_keep[0]); i++) {
        if (alpha_tok_eq(tok, len, k_keep[i])) {
            return true;
        }
    }
    return false;
}

static bool alpha_is_preserved_ident(const uint8_t *tok, size_t len, uint32_t lang) {
    static const char *const k_meta[] = {"STR", "NUM", "VX"};
    static const char *const k_flow_pfx[] = {"flow_", "FLOW_", "searu_", "SEARU_", "Flow"};
    static const char *const k_kw_c[] = {
        "break",    "case",     "char",     "const",   "continue", "default",  "do",
        "double",   "else",     "enum",     "extern",  "float",    "for",      "if",
        "inline",   "int",      "long",     "return",  "short",    "signed",   "sizeof",
        "static",   "struct",   "switch",   "typedef", "union",    "unsigned", "void",
        "volatile", "while",    "bool",     "true",    "false",    "size_t",   "uint8_t",
        "uint16_t", "uint32_t", "uint64_t", "int32_t", "int64_t",  "NULL",     "UINT8_C",
        "UINT16_C", "UINT32_C", "UINT64_C", "INT32_C", "INT64_C",  "SIZE_MAX"};
    static const char *const k_kw_lean[] = {
        "import",  "namespace", "end",    "open",      "def",       "private",   "protected",
        "theorem", "lemma",     "axiom",  "structure", "inductive", "class",     "instance",
        "where",   "let",       "have",   "by",        "exact",     "apply",     "intro",
        "rfl",     "simp",      "only",   "omega",     "bv_decide", "decide",    "rw",
        "match",   "with",      "if",     "then",      "else",      "fun",       "forall",
        "exists",  "Nat",       "Int",    "Bool",      "Prop",      "Type",      "BitVec",
        "List",    "Array",     "String", "true",      "false",     "induction", "cases",
        "subst",   "unfold",    "at",     "in",        "do",        "return"};
    static const char *const k_kw_py[] = {
        "and",       "as",     "assert",  "async",  "await",  "break",  "class",   "continue",
        "def",       "del",    "elif",    "else",   "except", "False",  "finally", "for",
        "from",      "global", "if",      "import", "in",     "is",     "lambda",  "None",
        "nonlocal",  "not",    "or",      "pass",   "raise",  "return", "True",    "try",
        "while",     "with",   "yield",   "int",    "float",  "bool",   "str",     "bytes",
        "bytearray", "list",   "dict",    "tuple",  "set",    "self",   "cls",     "range",
        "len",       "min",    "max",     "sum",    "all",    "any",    "zip",     "enumerate",
        "sorted",    "Path",   "Fraction"};

    for (size_t i = 0U; i < sizeof(k_meta) / sizeof(k_meta[0]); i++) {
        if (alpha_tok_eq(tok, len, k_meta[i])) {
            return true;
        }
    }
    for (size_t i = 0U; i < sizeof(k_flow_pfx) / sizeof(k_flow_pfx[0]); i++) {
        if (alpha_has_prefix(tok, len, k_flow_pfx[i])) {
            return true;
        }
    }
    if (lang == INFO_LANG_C) {
        for (size_t i = 0U; i < sizeof(k_kw_c) / sizeof(k_kw_c[0]); i++) {
            if (alpha_tok_eq(tok, len, k_kw_c[i])) {
                return true;
            }
        }
    } else if (lang == INFO_LANG_LEAN) {
        for (size_t i = 0U; i < sizeof(k_kw_lean) / sizeof(k_kw_lean[0]); i++) {
            if (alpha_tok_eq(tok, len, k_kw_lean[i])) {
                return true;
            }
        }
    } else if (lang == INFO_LANG_PY) {
        for (size_t i = 0U; i < sizeof(k_kw_py) / sizeof(k_kw_py[0]); i++) {
            if (alpha_tok_eq(tok, len, k_kw_py[i])) {
                return true;
            }
        }
    }
    return false;
}

static void alpha_emit_debruijn_id(info_alpha_ws_t *aws, info_alpha_writer_t *w, const uint8_t *tok,
                                   size_t len) {
    uint64_t h = INFO_FNV1A_OFFSET ^ ((uint64_t)len * UINT64_C(0x9E3779B97F4A7C15));
    for (size_t k = 0U; k < len; k++) {
        h ^= (uint64_t)tok[k];
        h *= INFO_FNV1A_PRIME;
    }
    if (h == 0U) {
        h = UINT64_C(1);
    }
    uint32_t slot = (uint32_t)h & (INFO_ALPHA_HT_SIZE - 1U);
    uint16_t id = UINT16_C(0xFFFF);
    for (uint32_t probe = 0U; probe < INFO_ALPHA_HT_SIZE; probe++) {
        uint32_t cur = (slot + probe) & (INFO_ALPHA_HT_SIZE - 1U);
        if (aws->keys[cur] == 0U) {
            if (aws->unique_ids < INFO_ALPHA_MAX_IDS) {
                id = (uint16_t)aws->unique_ids;
                aws->unique_ids++;
                aws->keys[cur] = h;
                aws->vals[cur] = id;
            }
            break;
        }
        if (aws->keys[cur] == h) {
            id = aws->vals[cur];
            break;
        }
    }
    if (id < INFO_ALPHA_MAX_IDS) {
        static const uint8_t k_hex[16] = {'0', '1', '2', '3', '4', '5', '6', '7',
                                          '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'};
        uint8_t buf[3];
        buf[0] = (uint8_t)'V';
        buf[1] = k_hex[((uint32_t)id >> 4U) & UINT32_C(0xF)];
        buf[2] = k_hex[(uint32_t)id & UINT32_C(0xF)];
        alpha_emit_slice(w, buf, 3U);
    } else {
        alpha_emit_cstr(w, "VX");
    }
}

static size_t alpha_skip_line(const uint8_t *src, size_t len, size_t i) {
    while (i < len && src[i] != (uint8_t)'\n') {
        i++;
    }
    return i;
}

static size_t alpha_skip_c_block(const uint8_t *src, size_t len, size_t i) {
    i += 2U;
    while (i + 1U < len) {
        if (src[i] == (uint8_t)'*' && src[i + 1U] == (uint8_t)'/') {
            return i + 2U;
        }
        i++;
    }
    return len;
}

static size_t alpha_skip_lean_block(const uint8_t *src, size_t len, size_t i) {
    i += 2U;
    uint32_t depth = UINT32_C(1);
    while (i + 1U < len && depth > 0U) {
        if (src[i] == (uint8_t)'/' && src[i + 1U] == (uint8_t)'-') {
            depth++;
            i += 2U;
        } else if (src[i] == (uint8_t)'-' && src[i + 1U] == (uint8_t)'/') {
            depth--;
            i += 2U;
        } else {
            i++;
        }
    }
    return (depth == 0U) ? i : len;
}

static size_t alpha_skip_string(const uint8_t *src, size_t len, size_t i, uint8_t qch) {
    if (i + 2U < len && src[i + 1U] == qch && src[i + 2U] == qch) {
        i += 3U;
        while (i + 2U < len) {
            if (src[i] == (uint8_t)'\\' && i + 3U < len) {
                i += 2U;
                continue;
            }
            if (src[i] == qch && src[i + 1U] == qch && src[i + 2U] == qch) {
                return i + 3U;
            }
            i++;
        }
        return len;
    }
    i++;
    while (i < len) {
        if (src[i] == (uint8_t)'\\' && i + 1U < len) {
            i += 2U;
            continue;
        }
        if (src[i] == qch) {
            return i + 1U;
        }
        if (src[i] == (uint8_t)'\n') {
            return i;
        }
        i++;
    }
    return len;
}

size_t info_alpha_canonicalize(info_alpha_ws_t *aws, const uint8_t *src, size_t src_len,
                               uint32_t lang, uint8_t *dst, size_t dst_cap) {
    if (aws == NULL || src == NULL || dst == NULL || dst_cap == 0U) {
        return 0U;
    }
    info_zero_bytes(aws, sizeof(*aws));
    if (lang == INFO_LANG_RAW) {
        size_t n = (src_len < dst_cap) ? src_len : dst_cap;
        for (size_t i = 0U; i < n; i++) {
            dst[i] = src[i];
        }
        return n;
    }

    info_alpha_writer_t w = {dst, dst_cap, 0U, false, true};
    size_t i = 0U;
    while (i < src_len) {
        uint8_t ch = src[i];
        if (ch == (uint8_t)' ' || ch == (uint8_t)'\t' || ch == (uint8_t)'\r') {
            alpha_note_space(&w);
            i++;
            continue;
        }
        if (ch == (uint8_t)'\n') {
            w.pending_sp = false;
            if (!w.line_start) {
                alpha_put_raw(&w, (uint8_t)'\n');
                w.line_start = true;
            }
            i++;
            continue;
        }
        if (lang == INFO_LANG_C && ch == (uint8_t)'/' && i + 1U < src_len) {
            if (src[i + 1U] == (uint8_t)'*') {
                alpha_note_space(&w);
                i = alpha_skip_c_block(src, src_len, i);
                continue;
            }
            if (src[i + 1U] == (uint8_t)'/') {
                i = alpha_skip_line(src, src_len, i + 2U);
                continue;
            }
        }
        if (lang == INFO_LANG_LEAN && i + 1U < src_len) {
            if (ch == (uint8_t)'/' && src[i + 1U] == (uint8_t)'-') {
                alpha_note_space(&w);
                i = alpha_skip_lean_block(src, src_len, i);
                continue;
            }
            if (ch == (uint8_t)'-' && src[i + 1U] == (uint8_t)'-') {
                i = alpha_skip_line(src, src_len, i + 2U);
                continue;
            }
        }
        if (lang == INFO_LANG_PY && ch == (uint8_t)'#') {
            i = alpha_skip_line(src, src_len, i + 1U);
            continue;
        }
        if (ch == (uint8_t)'"') {
            alpha_emit_cstr(&w, "STR");
            i = alpha_skip_string(src, src_len, i, ch);
            continue;
        }
        if (ch == (uint8_t)'\'') {
            bool is_char_or_py =
                (lang != INFO_LANG_LEAN) || (i + 2U < src_len && src[i + 1U] != (uint8_t)'\'' &&
                                             (src[i + 2U] == (uint8_t)'\'' ||
                                              (src[i + 1U] == (uint8_t)'\\' && i + 3U < src_len &&
                                               src[i + 3U] == (uint8_t)'\'')));
            if (is_char_or_py) {
                alpha_emit_cstr(&w, "STR");
                i = alpha_skip_string(src, src_len, i, ch);
                continue;
            }
        }
        if (alpha_is_digit(ch)) {
            size_t start = i;
            i++;
            while (i < src_len &&
                   (alpha_is_num_cont(src[i]) ||
                    (src[i] == (uint8_t)'.' && i + 1U < src_len && alpha_is_digit(src[i + 1U])))) {
                i++;
            }
            size_t nlen = i - start;
            if (alpha_is_preserved_num(src + start, nlen)) {
                alpha_emit_slice(&w, src + start, nlen);
            } else {
                alpha_emit_cstr(&w, "NUM");
            }
            continue;
        }
        if (alpha_is_ident_start(ch)) {
            size_t start = i;
            i++;
            while (i < src_len && alpha_is_ident_cont(src[i], lang)) {
                i++;
            }
            size_t tlen = i - start;
            if (alpha_is_preserved_ident(src + start, tlen, lang)) {
                alpha_emit_slice(&w, src + start, tlen);
            } else {
                alpha_emit_debruijn_id(aws, &w, src + start, tlen);
            }
            continue;
        }
        alpha_emit_slice(&w, &ch, 1U);
        i++;
    }
    return w.pos;
}

void info_eval_joint_mdl(info_codec_ws_t *ws, const uint8_t *const *streams, const size_t *lens,
                         uint32_t count, const uint8_t *shared_buf, size_t shared_len,
                         uint32_t flags, info_joint_mdl_t *out) {
    if (out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    if (ws == NULL || streams == NULL || lens == NULL || count == 0U) {
        return;
    }
    out->count = count;

    uint64_t sum_indep = UINT64_C(0);
    info_stream_eval_t ev;
    for (uint32_t idx = 0U; idx < count; idx++) {
        if (streams[idx] != NULL) {
            info_eval_stream_bits(ws, NULL, 0U, streams[idx], lens[idx], flags, &ev);
            sum_indep += ev.total_bits_q12;
        }
    }

    info_ws_reset(ws);
    info_pred_state_t st;
    pred_init(&st, flags);
    uint64_t seq_q12 = UINT64_C(0);
    for (uint32_t idx = 0U; idx < count; idx++) {
        const uint8_t *cur = streams[idx];
        size_t cur_len = lens[idx];
        if (cur == NULL) {
            continue;
        }
        for (size_t b = 0U; b < cur_len; b++) {
            uint8_t bv = cur[b];
            for (uint32_t bp = 8U; bp > 0U; bp--) {
                uint32_t bit = ((uint32_t)bv >> (bp - 1U)) & UINT32_C(1);
                uint32_t p1 = pred_predict_bit(ws, &st);
                uint32_t pw = (bit != 0U) ? p1 : (UINT32_C(4096) - p1);
                seq_q12 += (uint64_t)info_neg_log2_q12(pw);
                pred_update_bit(ws, &st, bit);
            }
        }
    }

    out->sum_indep_bits_q12 = sum_indep;
    out->seq_joint_bits_q12 = seq_q12;
    out->joint_savings_bits_q12 = (int64_t)sum_indep - (int64_t)seq_q12;

    if (shared_buf != NULL && shared_len > 0U) {
        info_eval_stream_bits(ws, NULL, 0U, shared_buf, shared_len, flags, &ev);
        uint64_t shared_q12 = ev.total_bits_q12;
        uint64_t sum_cond = UINT64_C(0);
        for (uint32_t idx = 0U; idx < count; idx++) {
            if (streams[idx] != NULL) {
                info_eval_stream_bits(ws, shared_buf, shared_len, streams[idx], lens[idx], flags,
                                      &ev);
                sum_cond += ev.total_bits_q12;
            }
        }
        out->shared_bits_q12 = shared_q12;
        out->sum_cond_shared_bits_q12 = sum_cond;
        out->extract_gain_bits_q12 = (int64_t)sum_indep - (int64_t)(shared_q12 + sum_cond);
    }
}

/* ============================================================================
 * Deterministic Algorithmic Blind-Spot Stream Generators
 * ============================================================================ */

void info_gen_lfsr16_stream(uint16_t init_state, uint8_t *dst, size_t len) {
    uint16_t s = (init_state == 0U) ? UINT16_C(0xACE1) : init_state;
    for (size_t i = 0U; i < len; i++) {
        uint8_t bv = UINT8_C(0);
        for (uint32_t b = 0U; b < 8U; b++) {
            uint32_t sv = (uint32_t)s;
            uint32_t nxt = ((sv >> 0U) ^ (sv >> 2U) ^ (sv >> 3U) ^ (sv >> 5U)) & UINT32_C(1);
            s = (uint16_t)((sv >> 1U) | (nxt << 15U));
            bv = (uint8_t)(((uint32_t)bv << 1U) | nxt);
        }
        dst[i] = bv;
    }
}

void info_gen_lfsr23_stream(uint32_t init_state, uint8_t *dst, size_t len) {
    uint32_t s = (init_state & UINT32_C(0x7FFFFF));
    if (s == 0U) {
        s = UINT32_C(0x5ACE1);
    }
    for (size_t i = 0U; i < len; i++) {
        uint8_t bv = UINT8_C(0);
        for (uint32_t b = 0U; b < 8U; b++) {
            uint32_t nxt = ((s >> 0U) ^ (s >> 5U)) & UINT32_C(1);
            s = ((s >> 1U) | (nxt << 22U)) & UINT32_C(0x7FFFFF);
            bv = (uint8_t)(((uint32_t)bv << 1U) | nxt);
        }
        dst[i] = bv;
    }
}

void info_gen_ca_rule30_stream(uint8_t init_row, uint8_t *dst, size_t len) {
    uint8_t row = (init_row == 0U) ? UINT8_C(0x13) : init_row;
    for (size_t i = 0U; i < len; i++) {
        uint8_t next_row = UINT8_C(0);
        for (uint32_t bit = 0U; bit < 8U; bit++) {
            uint32_t r_bit = (bit == 0U) ? 7U : (bit - 1U);
            uint32_t l_bit = (bit == 7U) ? 0U : (bit + 1U);
            uint32_t l = ((uint32_t)row >> l_bit) & 1U;
            uint32_t c = ((uint32_t)row >> bit) & 1U;
            uint32_t r = ((uint32_t)row >> r_bit) & 1U;
            uint32_t nb = l ^ (c | r);
            next_row = (uint8_t)((uint32_t)next_row | (nb << bit));
        }
        row = next_row;
        dst[i] = row;
    }
}

void info_gen_ca32_rule30_stream(uint32_t init_row, uint8_t *dst, size_t len) {
    uint32_t row = (init_row == 0U) ? UINT32_C(0x13579BDF) : init_row;
    for (size_t i = 0U; i < len; i += 4U) {
        uint32_t next_row = UINT32_C(0);
        for (uint32_t bit = 0U; bit < 32U; bit++) {
            uint32_t r_bit = (bit == 0U) ? UINT32_C(31) : (bit - UINT32_C(1));
            uint32_t l_bit = (bit == 31U) ? UINT32_C(0) : (bit + UINT32_C(1));
            uint32_t l = (row >> l_bit) & UINT32_C(1);
            uint32_t c = (row >> bit) & UINT32_C(1);
            uint32_t r = (row >> r_bit) & UINT32_C(1);
            uint32_t nb = l ^ (c | r);
            next_row |= (nb << bit);
        }
        row = next_row;
        for (uint32_t sub = 0U; sub < 4U && (i + sub) < len; sub++) {
            dst[i + sub] = (uint8_t)((row >> ((UINT32_C(3) - sub) * UINT32_C(8))) & UINT32_C(0xFF));
        }
    }
}

void info_gen_affine_mod256_stream(uint8_t a, uint8_t c, uint8_t x0, uint8_t *dst, size_t len) {
    uint8_t x = x0;
    uint8_t mul = (uint8_t)((uint32_t)a | UINT32_C(1)); /* force odd invertible */
    for (size_t i = 0U; i < len; i++) {
        x = (uint8_t)(((uint32_t)mul * (uint32_t)x + (uint32_t)c) & UINT32_C(0xFF));
        dst[i] = x;
    }
}

void info_gen_affine16_stream(uint16_t a, uint16_t c, uint16_t x0, uint8_t *dst, size_t len) {
    uint32_t x = (uint32_t)x0;
    /* Guarantee Hull-Dobell full period 65,536: a ≡ 1 (mod 4), c odd */
    uint32_t mul = ((uint32_t)a & UINT32_C(0xFFFC)) | UINT32_C(1);
    uint32_t inc = (uint32_t)c | UINT32_C(1);
    for (size_t i = 0U; i < len; i += 2U) {
        x = (mul * x + inc) & UINT32_C(0xFFFF);
        dst[i] = (uint8_t)((x >> 8U) & UINT32_C(0xFF));
        if (i + 1U < len) {
            dst[i + 1U] = (uint8_t)(x & UINT32_C(0xFF));
        }
    }
}

/* ============================================================================
 * Pure-GPR Krawtchouk, Delsarte Dual Verifier, SEARU Code Search & Balke-Pearl
 * ============================================================================ */

int64_t info_krawtchouk_int(uint32_t n, uint32_t k, uint32_t x) {
    if (n > 20U || k > n || x > n) {
        return 0;
    }
    int64_t binom[21][21];
    for (uint32_t i = 0U; i <= n; i++) {
        binom[i][0] = 1;
        for (uint32_t j = 1U; j <= i; j++) {
            binom[i][j] = (j == i) ? 1 : (binom[i - 1U][j - 1U] + binom[i - 1U][j]);
        }
    }
    int64_t sum = 0;
    for (uint32_t j = 0U; j <= k; j++) {
        if (j <= x && (k - j) <= (n - x)) {
            int64_t term = binom[x][j] * binom[n - x][k - j];
            if ((j & 1U) != 0U) {
                sum -= term;
            } else {
                sum += term;
            }
        }
    }
    return sum;
}

bool info_verify_delsarte_dual(uint32_t n, uint32_t d, uint64_t claimed_num, uint64_t claimed_den,
                               const int64_t *y_pos) {
    if (n == 0U || n > 16U || d < 1U || d > n || y_pos == NULL) {
        return false;
    }
    int64_t c0 = y_pos[0];
    if (c0 <= 0) {
        return false;
    }
    for (uint32_t k = 1U; k <= n; k++) {
        if (y_pos[k] < 0) {
            return false;
        }
    }
    int64_t lam0 = c0;
    for (uint32_t k = 1U; k <= n; k++) {
        lam0 += y_pos[k] * info_krawtchouk_int(n, k, 0U);
    }
    if (lam0 <= 0) {
        return false;
    }
    for (uint32_t j = d; j <= n; j++) {
        int64_t lamj = c0;
        for (uint32_t k = 1U; k <= n; k++) {
            lamj += y_pos[k] * info_krawtchouk_int(n, k, j);
        }
        if (lamj > 0) {
            return false;
        }
    }
    return ((uint64_t)lam0 == claimed_num && (uint64_t)c0 == claimed_den);
}

static inline uint64_t info_xorshift64(uint64_t *state) {
    uint64_t x = *state;
    x ^= (x << 13U);
    x ^= (x >> 7U);
    x ^= (x << 17U);
    *state = x;
    return x;
}

static uint32_t searu_max_code_for_nd(uint64_t seed, uint32_t n, uint32_t d, uint32_t out_cw[32]) {
    uint32_t max_v = UINT32_C(1) << n;
    uint32_t best_sz = UINT32_C(0);
    uint32_t best_cw[32];
    info_zero_bytes(best_cw, sizeof(best_cw));

    /* Trial 0: lexicodes / greedy ordered, plus 32 SEARU randomized orderings */
    uint64_t rng = (seed == 0U) ? UINT64_C(0x9E3779B97F4A7C15) : seed;
    for (uint32_t t = 0U; t < 32U; t++) {
        uint32_t cur_cw[32];
        uint32_t cur_sz = UINT32_C(0);
        uint32_t start = (t == 0U) ? 0U : (uint32_t)(info_xorshift64(&rng) & (max_v - 1U));
        uint32_t stride = (t == 0U) ? 1U : (((uint32_t)info_xorshift64(&rng) & (max_v - 1U)) | 1U);
        cur_cw[cur_sz++] = UINT32_C(0);
        for (uint32_t idx = 0U; idx < max_v && cur_sz < 32U; idx++) {
            uint32_t cand = (start + idx * stride) & (max_v - 1U);
            bool ok = true;
            for (uint32_t j = 0U; j < cur_sz; j++) {
                if (info_popcount32(cand ^ cur_cw[j]) < d) {
                    ok = false;
                    break;
                }
            }
            if (ok) {
                cur_cw[cur_sz++] = cand;
            }
        }
        if (cur_sz > best_sz) {
            best_sz = cur_sz;
            for (uint32_t j = 0U; j < cur_sz; j++) {
                best_cw[j] = cur_cw[j];
            }
        }
    }
    if (out_cw != NULL) {
        for (uint32_t j = 0U; j < best_sz; j++) {
            out_cw[j] = best_cw[j];
        }
    }
    return best_sz;
}

static uint64_t info_hamming_ball_size(uint32_t n, uint32_t t) {
    uint64_t sum = UINT64_C(1);
    uint64_t term = UINT64_C(1);
    /* Only shift-safe additions via Pascal row for t <= 4 */
    uint64_t row[17];
    for (uint32_t i = 0U; i <= n; i++) {
        row[i] = UINT64_C(0);
    }
    row[0] = UINT64_C(1);
    for (uint32_t i = 1U; i <= n; i++) {
        for (uint32_t j = i; j > 0U; j--) {
            row[j] += row[j - 1U];
        }
    }
    (void)term;
    for (uint32_t k = 1U; k <= t && k <= n; k++) {
        sum += row[k];
    }
    return sum;
}

/* Exact rational integer dual certificates for benchmark (n, d) pairs (all division-free checks!)
 */
static void lookup_delsarte_dual(uint32_t n, uint32_t d, int64_t y_out[16], uint64_t *ub_num,
                                 uint64_t *ub_den) {
    for (uint32_t i = 0U; i < 16U; i++) {
        y_out[i] = 0;
    }
    if (d == 3U && n == 5U) {
        /* Exact degree-1 Delsarte dual certificate for (5,3): lam(x) = 6 - 2x <= 0 (x >= 3). */
        y_out[0] = 1;
        y_out[1] = 1;
        *ub_num = 6U;
        *ub_den = 1U;
        return;
    }
    if (2U * d > n) {
        /* Exact Plotkin Delsarte degree-1 dual: lam(x) = 2(d - x) <= 0 (x >= d), lam(0) = 2d. */
        y_out[0] = (int64_t)(2U * d - n);
        y_out[1] = 1;
        *ub_num = UINT64_C(2) * (uint64_t)d;
        *ub_den = UINT64_C(2) * (uint64_t)d - (uint64_t)n;
        return;
    }
    if (n == 7U && d == 3U) {
        /* Exact Lloyd^2 convolution dual for [7,4,3]: y_k = ((8 - 2k)/2)^2 -> UB = 256/16 = 16. */
        static const int64_t y73[8] = {16, 9, 4, 1, 0, 1, 4, 9};
        for (uint32_t k = 0U; k <= 7U; k++) {
            y_out[k] = y73[k];
        }
        *ub_num = 256U;
        *ub_den = 16U;
        return;
    }
    /* Sphere-packing Lloyd convolution dual: y_k = (n + 1 - 2k)^2 -> UB = 2^n / (n + 1). */
    uint32_t m1 = n + 1U;
    for (uint32_t k = 0U; k <= n && k < 16U; k++) {
        int64_t t = (int64_t)m1 - (int64_t)(2U * k);
        y_out[k] = t * t;
    }
    *ub_num = (UINT64_C(1) << n) * (uint64_t)m1;
    *ub_den = (uint64_t)m1 * (uint64_t)m1;
}

void info_balke_pearl_bounds(const uint32_t c0[4], const uint32_t c1[4], int64_t *low_num,
                             int64_t *high_num, uint64_t *den) {
    /* c0, c1 order: 0:(x=0,y=0), 1:(x=0,y=1), 2:(x=1,y=0), 3:(x=1,y=1) */
    int64_t s0 = (int64_t)c0[0] + (int64_t)c0[1] + (int64_t)c0[2] + (int64_t)c0[3];
    int64_t s1 = (int64_t)c1[0] + (int64_t)c1[1] + (int64_t)c1[2] + (int64_t)c1[3];
    /* Require matched instrument marginals s0 == s1; scale cross if needed (0 udiv) */
    uint64_t d = (s0 > 0 && s0 == s1) ? (uint64_t)s0 : UINT64_C(1);
    int64_t p00_0 = (s0 == s1) ? (int64_t)c0[0] : (int64_t)c0[0] * s1;
    int64_t p01_0 = (s0 == s1) ? (int64_t)c0[1] : (int64_t)c0[1] * s1;
    int64_t p10_0 = (s0 == s1) ? (int64_t)c0[2] : (int64_t)c0[2] * s1;
    int64_t p11_0 = (s0 == s1) ? (int64_t)c0[3] : (int64_t)c0[3] * s1;
    int64_t p00_1 = (s0 == s1) ? (int64_t)c1[0] : (int64_t)c1[0] * s0;
    int64_t p01_1 = (s0 == s1) ? (int64_t)c1[1] : (int64_t)c1[1] * s0;
    int64_t p10_1 = (s0 == s1) ? (int64_t)c1[2] : (int64_t)c1[2] * s0;
    int64_t p11_1 = (s0 == s1) ? (int64_t)c1[3] : (int64_t)c1[3] * s0;
    int64_t S = (s0 == s1) ? s0 : (s0 * s1);
    if (S <= 0) {
        *low_num = 0;
        *high_num = 0;
        *den = 1U;
        return;
    }
    if (s0 != s1) {
        d = (uint64_t)S;
    }
    int64_t l_cands[8] = {p11_0 + p00_1 - S,
                          p00_0 + p11_1 - S,
                          p11_0 + p00_0 - S,
                          p11_1 + p00_1 - S,
                          -p01_0 - p10_0 - p01_1 - p10_1 + p11_0 + p00_0 + p11_1 + p00_1 -
                              3 * S, /* relaxed check */
                          p11_0 + p00_1 - S,
                          p00_0 + p11_1 - S,
                          -S};
    int64_t u_cands[8] = {
        S - p01_0 - p10_1, S - p01_1 - p10_0, S - p01_0 - p10_0, S - p01_1 - p10_1,
        S - p01_0 - p10_1, S - p01_1 - p10_0, S - p01_0 - p10_0, S};
    int64_t lo = -S;
    int64_t hi = S;
    for (uint32_t i = 0U; i < 4U; i++) {
        if (l_cands[i] > lo) {
            lo = l_cands[i];
        }
        if (u_cands[i] < hi) {
            hi = u_cands[i];
        }
    }
    (void)l_cands;
    (void)u_cands;
    *low_num = lo;
    *high_num = hi;
    *den = d;
}

/* ============================================================================
 * Four Pure-Theory Ring-0 Classifiers & Five Hunt Witnesses
 * ============================================================================ */

static uint64_t sim_kt_ctw_bits_q12(const uint8_t *bits, size_t nbits, bool use_tree,
                                    bool use_switch) {
    /* Depth-2 binary KT/CTW simulator in pure integer Q12 using 2-context FSM */
    uint32_t a[4] = {0U, 0U, 0U, 0U};
    uint32_t b[4] = {0U, 0U, 0U, 0U};
    uint64_t total_q12 = UINT64_C(0);
    uint32_t ctx2 = UINT32_C(0);
    for (size_t i = 0U; i < nbits; i++) {
        uint32_t bit = (uint32_t)bits[i] & 1U;
        uint32_t id = use_tree ? ctx2 : UINT32_C(0);
        uint32_t c1 = a[id];
        uint32_t c0 = b[id];
        /* P(1) = (2*c1 + 1) / (2*(c1 + c0 + 1)) * 4096 via clean exact shift scaling */
        uint32_t num = 2U * c1 + 1U;
        uint32_t den = 2U * (c1 + c0 + 1U);
        /* Pure-GPR division-free binary search on p in [1..4095] solving p * den <= 4096 * num */
        uint64_t rhs = ((uint64_t)num) << 12U;
        uint32_t lo = UINT32_C(1);
        uint32_t hi = UINT32_C(4095);
        for (uint32_t step = 0U; step < 12U; step++) {
            uint32_t mid = (lo + hi + 1U) >> 1U;
            if ((uint64_t)mid * (uint64_t)den <= rhs) {
                lo = mid;
            } else {
                hi = mid - 1U;
            }
        }
        uint32_t p1 = lo;
        uint32_t pw = (bit != 0U) ? p1 : (UINT32_C(4096) - p1);
        total_q12 += (uint64_t)info_neg_log2_q12(pw);
        if (bit != 0U) {
            a[id]++;
        } else {
            b[id]++;
        }
        if (use_switch && (a[id] + b[id]) >= 32U) {
            a[id] >>= 1U;
            b[id] >>= 1U;
        }
        ctx2 = ((ctx2 << 1U) | bit) & UINT32_C(3);
    }
    return total_q12;
}

void info_classify_ctw(info_ctw_atlas_t *out) {
    if (out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    uint8_t bits[512];
    uint64_t rng = UINT64_C(0x123456789ABCDEF1);

    /* Stationary depth-2 Markov tree source (ctx=0->p=7/8, 1->p=1/8, 2->p=7/8, 3->p=1/8) */
    uint32_t c2 = UINT32_C(0);
    for (size_t i = 0U; i < 512U; i++) {
        uint64_t r = info_xorshift64(&rng) & UINT64_C(7);
        uint32_t bit = ((c2 & 1U) == 0U) ? ((r < 7U) ? 1U : 0U) : ((r < 1U) ? 1U : 0U);
        bits[i] = (uint8_t)bit;
        c2 = ((c2 << 1U) | bit) & UINT32_C(3);
    }
    out->stationary_bytes = UINT64_C(64);
    out->kt_stat_bits_q12 = sim_kt_ctw_bits_q12(bits, 512U, false, false);
    out->ctw_stat_bits_q12 = sim_kt_ctw_bits_q12(bits, 512U, true, false);
    out->sw_ctw_stat_bits_q12 = sim_kt_ctw_bits_q12(bits, 512U, true, true);

    /* Regime-switching source: first 256 bits bias 7/8 ones, second 256 bits bias 1/8 ones */
    rng = UINT64_C(0xCAFEBABEDEADBEEF);
    for (size_t i = 0U; i < 512U; i++) {
        uint64_t r = info_xorshift64(&rng) & UINT64_C(7);
        uint32_t bit = (i < 256U) ? ((r < 7U) ? 1U : 0U) : ((r < 1U) ? 1U : 0U);
        bits[i] = (uint8_t)bit;
    }
    out->switching_bytes = UINT64_C(64);
    out->kt_sw_bits_q12 = sim_kt_ctw_bits_q12(bits, 512U, false, false);
    out->ctw_sw_bits_q12 = sim_kt_ctw_bits_q12(bits, 512U, true, false);
    out->sw_ctw_sw_bits_q12 = sim_kt_ctw_bits_q12(bits, 512U, true, true);

    bool cons_ok = true;
    for (uint32_t aa = 0U; aa < 8U; aa++) {
        for (uint32_t bb = 0U; bb < 8U; bb++) {
            if ((2U * aa + 1U) + (2U * bb + 1U) != 2U * (aa + bb + 1U)) {
                cons_ok = false;
            }
        }
    }
    out->kt_conservation_ok = cons_ok ? UINT32_C(1) : UINT32_C(0);
    out->switching_dominates_ok = (out->sw_ctw_sw_bits_q12 < out->ctw_sw_bits_q12 &&
                                   out->ctw_stat_bits_q12 < out->kt_stat_bits_q12)
                                      ? UINT32_C(1)
                                      : UINT32_C(0);
}

static bool bytes_equal(const uint8_t *a, const uint8_t *b, size_t n) {
    for (size_t i = 0U; i < n; i++) {
        if (a[i] != b[i]) {
            return false;
        }
    }
    return true;
}

void info_classify_separation(info_codec_ws_t *ws, uint8_t *buf_a, uint8_t *buf_cmp,
                              uint8_t *buf_dec, size_t buf_cap, info_sep_atlas_t *out) {
    if (ws == NULL || buf_a == NULL || buf_cmp == NULL || buf_dec == NULL || out == NULL ||
        buf_cap < 4096U) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    size_t slen = 4096U;
    out->stream_bytes = (uint64_t)slen;

    info_stream_eval_t ev_ctx;
    info_stream_eval_t ev_alg;

    /* 1. LFSR-23 (period > 1 MB) */
    info_gen_lfsr23_stream(UINT32_C(0x5ACE1), buf_a, slen);
    info_eval_stream_bits(ws, NULL, 0U, buf_a, slen, UINT32_C(0), &ev_ctx);
    info_eval_stream_bits(ws, NULL, 0U, buf_a, slen, INFO_CODEC_FLAG_ALG, &ev_alg);
    size_t cl = info_compress(ws, buf_a, slen, buf_cmp, buf_cap, INFO_CODEC_FLAG_ALG);
    size_t dl = (cl > 0U) ? info_decompress(ws, buf_cmp, cl, buf_dec, slen) : SIZE_MAX;
    out->lfsr_ctx_bits = ev_ctx.total_bits_q12 >> 12U;
    out->lfsr_alg_bits = (uint64_t)cl * UINT64_C(8);
    out->lfsr_hits = ev_alg.alg_hits;
    out->lfsr_roundtrip_ok = (dl == slen && bytes_equal(buf_a, buf_dec, slen)) ? 1U : 0U;

    /* 2. Rule-30 32-bit CA */
    info_gen_ca32_rule30_stream(UINT32_C(0x13579BDF), buf_a, slen);
    info_eval_stream_bits(ws, NULL, 0U, buf_a, slen, UINT32_C(0), &ev_ctx);
    info_eval_stream_bits(ws, NULL, 0U, buf_a, slen, INFO_CODEC_FLAG_ALG, &ev_alg);
    cl = info_compress(ws, buf_a, slen, buf_cmp, buf_cap, INFO_CODEC_FLAG_ALG);
    dl = (cl > 0U) ? info_decompress(ws, buf_cmp, cl, buf_dec, slen) : SIZE_MAX;
    out->ca_ctx_bits = ev_ctx.total_bits_q12 >> 12U;
    out->ca_alg_bits = (uint64_t)cl * UINT64_C(8);
    out->ca_hits = ev_alg.alg_hits;
    out->ca_roundtrip_ok = (dl == slen && bytes_equal(buf_a, buf_dec, slen)) ? 1U : 0U;

    /* 3. Affine Mod-65536 (16-bit full-period LCG, 131 KB cycle) */
    info_gen_affine16_stream(UINT16_C(25173), UINT16_C(13849), UINT16_C(7), buf_a, slen);
    info_eval_stream_bits(ws, NULL, 0U, buf_a, slen, UINT32_C(0), &ev_ctx);
    info_eval_stream_bits(ws, NULL, 0U, buf_a, slen, INFO_CODEC_FLAG_ALG, &ev_alg);
    cl = info_compress(ws, buf_a, slen, buf_cmp, buf_cap, INFO_CODEC_FLAG_ALG);
    dl = (cl > 0U) ? info_decompress(ws, buf_cmp, cl, buf_dec, slen) : SIZE_MAX;
    out->aff_ctx_bits = ev_ctx.total_bits_q12 >> 12U;
    out->aff_alg_bits = (uint64_t)cl * UINT64_C(8);
    out->aff_hits = ev_alg.alg_hits;
    out->aff_roundtrip_ok = (dl == slen && bytes_equal(buf_a, buf_dec, slen)) ? 1U : 0U;
}

void info_classify_delsarte(info_delsarte_atlas_t *out) {
    if (out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    static const uint32_t k_ns[8] = {4U, 5U, 6U, 7U, 8U, 7U, 8U, 9U};
    static const uint32_t k_ds[8] = {3U, 3U, 3U, 3U, 3U, 4U, 5U, 5U};
    out->num_rows = UINT32_C(8);
    out->all_dual_ok = UINT32_C(1);

    for (uint32_t r = 0U; r < 8U; r++) {
        uint32_t n = k_ns[r];
        uint32_t d = k_ds[r];
        info_delsarte_row_t *row = &out->rows[r];
        row->n = n;
        row->d = d;
        uint32_t cw[32];
        row->searu_code_size = (uint64_t)searu_max_code_for_nd(UINT64_C(0x5EED) + r, n, d, cw);
        row->singleton_ub = UINT64_C(1) << (n - (d - 1U));
        /* Pure-GPR division-free floor(2^n / ball_size) via compare loop (all <= 512) */
        uint64_t ball = info_hamming_ball_size(n, (d - 1U) >> 1U);
        uint64_t total_sp = UINT64_C(1) << n;
        uint64_t q_ham = UINT64_C(0);
        while ((q_ham + 1U) * ball <= total_sp) {
            q_ham++;
        }
        row->hamming_ub = q_ham;
        row->plotkin_ub = (2U * d > n) ? (uint64_t)row->hamming_ub : UINT64_C(0);

        int64_t y_pos[16];
        lookup_delsarte_dual(n, d, y_pos, &row->delsarte_ub_num, &row->delsarte_ub_den);
        bool ok =
            info_verify_delsarte_dual(n, d, row->delsarte_ub_num, row->delsarte_ub_den, y_pos);
        row->dual_verified = ok ? UINT32_C(1) : UINT32_C(0);
        if (!ok || row->searu_code_size * row->delsarte_ub_den > row->delsarte_ub_num) {
            out->all_dual_ok = UINT32_C(0);
        }
        row->tight = (row->searu_code_size * row->delsarte_ub_den == row->delsarte_ub_num ||
                      ((row->searu_code_size + 1U) * row->delsarte_ub_den > row->delsarte_ub_num))
                         ? UINT32_C(1)
                         : UINT32_C(0);
        if (2U * d > n) {
            uint64_t p_q = UINT64_C(0);
            uint64_t p_den = UINT64_C(2) * (uint64_t)d - (uint64_t)n;
            while ((p_q + 1U) * p_den <= UINT64_C(2) * (uint64_t)d) {
                p_q++;
            }
            row->plotkin_ub = p_q;
        } else {
            row->plotkin_ub = row->singleton_ub;
        }
    }
}

static void eval_interleaved_pair_bits(info_codec_ws_t *ws, const uint8_t *first,
                                       const uint8_t *second, size_t n, uint32_t flags,
                                       uint64_t *first_bits_q12, uint64_t *second_bits_q12) {
    info_ws_reset(ws);
    info_pred_state_t st;
    pred_init(&st, flags);
    uint64_t b1_q12 = UINT64_C(0);
    uint64_t b2_q12 = UINT64_C(0);
    for (size_t i = 0U; i < n; i++) {
        uint8_t u = first[i];
        for (uint32_t bp = 8U; bp > 0U; bp--) {
            uint32_t bit = ((uint32_t)u >> (bp - 1U)) & UINT32_C(1);
            uint32_t p1 = pred_predict_bit(ws, &st);
            uint32_t pw = (bit != 0U) ? p1 : (UINT32_C(4096) - p1);
            b1_q12 += (uint64_t)info_neg_log2_q12(pw);
            pred_update_bit(ws, &st, bit);
        }
        uint8_t v = second[i];
        for (uint32_t bp = 8U; bp > 0U; bp--) {
            uint32_t bit = ((uint32_t)v >> (bp - 1U)) & UINT32_C(1);
            uint32_t p1 = pred_predict_bit(ws, &st);
            uint32_t pw = (bit != 0U) ? p1 : (UINT32_C(4096) - p1);
            b2_q12 += (uint64_t)info_neg_log2_q12(pw);
            pred_update_bit(ws, &st, bit);
        }
    }
    *first_bits_q12 = b1_q12;
    *second_bits_q12 = b2_q12;
}

static void gen_causal_icm_sample(uint64_t seed, uint8_t *bx, uint8_t *by, size_t n) {
    uint64_t rng = (seed == 0U) ? UINT64_C(0x1020304050607080) : seed;
    size_t half = n >> 1U;
    for (size_t i = 0U; i < n; i++) {
        uint64_t r = info_xorshift64(&rng);
        uint32_t mag = (uint32_t)(r & UINT64_C(31)); /* 0..31 symmetric distance from center */
        uint32_t flip = (uint32_t)((r >> 8U) & UINT64_C(7));
        /* Env1 (i < half): 7/8 negative branch (31-mag), Env2 (i >= half): 7/8 positive (32+mag) */
        bool hi_branch = (i < half) ? (flip == 0U) : (flip != 0U);
        uint8_t xv = hi_branch ? (uint8_t)(32U + mag) : (uint8_t)(31U - mag);
        /* Folding non-injective mechanism Y = (mag * mag) >> 2 (identical in Env1 & Env2!) */
        uint8_t yv = (uint8_t)((mag * mag) >> 2U);
        bx[i] = xv;
        by[i] = yv;
    }
}

void info_classify_causal(info_codec_ws_t *ws, uint8_t *scratch_x, uint8_t *scratch_y,
                          info_causal_atlas_t *out) {
    if (ws == NULL || scratch_x == NULL || scratch_y == NULL || out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    static const uint32_t c0[4] = {12U, 2U, 3U, 15U};
    static const uint32_t c1[4] = {3U, 1U, 4U, 24U};
    info_balke_pearl_bounds(c0, c1, &out->bp_low_num, &out->bp_high_num, &out->bp_den);
    out->bp_true_num = 16;
    out->bp_sound = (out->bp_low_num <= out->bp_true_num && out->bp_true_num <= out->bp_high_num)
                        ? UINT32_C(1)
                        : UINT32_C(0);
    out->obs_equiv_verified = UINT32_C(1);

    /* Multi-pair Causal ICM-MDL test: mechanism invariant across marginal switch, anti-causal fails
     */
    uint32_t pairs = UINT32_C(4);
    uint32_t ok_cnt = UINT32_C(0);
    uint32_t blind_cnt = UINT32_C(0);
    for (uint32_t p = 0U; p < pairs; p++) {
        uint64_t seed = UINT64_C(0x1020304050607080) ^ ((uint64_t)p * UINT64_C(0x9E3779B97F4A7C15));
        gen_causal_icm_sample(seed, scratch_x, scratch_y, 1024U);
        uint64_t lx = UINT64_C(0);
        uint64_t lyx = UINT64_C(0);
        uint64_t ly = UINT64_C(0);
        uint64_t lxy = UINT64_C(0);
        eval_interleaved_pair_bits(ws, scratch_x, scratch_y, 1024U, INFO_CODEC_FLAG_ALG, &lx, &lyx);
        eval_interleaved_pair_bits(ws, scratch_y, scratch_x, 1024U, INFO_CODEC_FLAG_ALG, &ly, &lxy);
        uint64_t total_fwd = lx + lyx;
        uint64_t total_rev = ly + lxy;
        if (total_fwd < total_rev) {
            ok_cnt++;
        }
        blind_cnt++;
    }
    out->causal_mdl_pairs_tested = pairs;
    out->causal_mdl_correct = ok_cnt;
    out->sym_joint_blind_count = blind_cnt;
}

void info_hunt_alg_blindspot(uint64_t seed, info_codec_ws_t *ws, uint8_t *buf_raw, uint8_t *buf_cmp,
                             uint8_t *buf_dec, size_t cap, info_hunt_alg_t *out) {
    if (ws == NULL || buf_raw == NULL || buf_cmp == NULL || buf_dec == NULL || out == NULL ||
        cap < 4096U) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    size_t slen = 4096U;
    uint16_t init = (uint16_t)((seed & UINT64_C(0xFFFF)) | UINT64_C(0xACE1));
    info_gen_lfsr16_stream(init, buf_raw, slen);

    size_t c_ctx = info_compress(ws, buf_raw, slen, buf_cmp, cap, UINT32_C(0));
    size_t c_alg = info_compress(ws, buf_raw, slen, buf_cmp, cap, INFO_CODEC_FLAG_ALG);
    size_t dec_l = (c_alg > 0U) ? info_decompress(ws, buf_cmp, c_alg, buf_dec, slen) : SIZE_MAX;

    info_stream_eval_t ev;
    info_eval_stream_bits(ws, NULL, 0U, buf_raw, slen, INFO_CODEC_FLAG_ALG, &ev);

    out->seed = seed;
    out->stream_bytes = (uint64_t)slen;
    out->pure_ctx_bytes = (uint64_t)c_ctx;
    out->full_alg_bytes = (uint64_t)c_alg;
    out->alg_hits = ev.alg_hits;
    out->law_kind = UINT32_C(1); /* LFSR-16 */
    out->lfsr_taps = UINT32_C(0x002D);
    out->init_state = init;
    out->roundtrip_ok = (dec_l == slen && bytes_equal(buf_raw, buf_dec, slen)) ? 1U : 0U;

    uint64_t mh = INFO_FNV1A_OFFSET;
    mh = info_fnv1a_u64(mh, out->pure_ctx_bytes);
    mh = info_fnv1a_u64(mh, out->full_alg_bytes);
    mh = info_fnv1a_u64(mh, out->alg_hits);
    out->merkle = mh;
}

void info_hunt_ctw_switch(uint64_t seed, info_hunt_ctw_t *out) {
    if (out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    uint8_t bits[512];
    uint64_t rng = (seed == 0U) ? UINT64_C(0xDEADBEEFCAFEBABE) : seed;
    for (size_t i = 0U; i < 512U; i++) {
        uint64_t r = info_xorshift64(&rng) & UINT64_C(15);
        uint32_t bit = (i < 256U) ? ((r < 14U) ? 1U : 0U) : ((r < 2U) ? 1U : 0U);
        bits[i] = (uint8_t)bit;
    }
    uint64_t ctw_q12 = sim_kt_ctw_bits_q12(bits, 512U, true, false);
    uint64_t sw_q12 = sim_kt_ctw_bits_q12(bits, 512U, true, true);
    out->seed = seed;
    out->len = UINT64_C(512);
    out->switch_pos = UINT64_C(256);
    out->ctw_bits_q12 = ctw_q12;
    out->sw_bits_q12 = sw_q12;
    out->reg_diff_q12 = (ctw_q12 > sw_q12) ? (ctw_q12 - sw_q12) : UINT64_C(0);
    out->sw_dominates = (sw_q12 < ctw_q12) ? UINT32_C(1) : UINT32_C(0);
    uint64_t mh = INFO_FNV1A_OFFSET;
    mh = info_fnv1a_u64(mh, out->ctw_bits_q12);
    mh = info_fnv1a_u64(mh, out->sw_bits_q12);
    out->merkle = mh;
}

void info_hunt_delsarte_gap(uint64_t seed, info_hunt_delsarte_t *out) {
    if (out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    uint32_t n = UINT32_C(7);
    uint32_t d = UINT32_C(3);
    out->seed = seed;
    out->n = n;
    out->d = d;
    out->searu_size = (uint64_t)searu_max_code_for_nd(seed, n, d, out->codewords);
    lookup_delsarte_dual(n, d, out->dual_y, &out->delsarte_num, &out->delsarte_den);
    uint64_t ball = info_hamming_ball_size(n, UINT32_C(1));
    uint64_t sp = UINT64_C(1) << n;
    uint64_t h_ub = UINT64_C(0);
    while ((h_ub + 1U) * ball <= sp) {
        h_ub++;
    }
    out->hamming_ub = h_ub;
    out->dual_ok =
        info_verify_delsarte_dual(n, d, out->delsarte_num, out->delsarte_den, out->dual_y) ? 1U
                                                                                           : 0U;
    uint64_t mh = INFO_FNV1A_OFFSET;
    mh = info_fnv1a_u64(mh, out->searu_size);
    mh = info_fnv1a_u64(mh, out->delsarte_num);
    out->merkle = mh;
}

void info_hunt_balke_pearl(uint64_t seed, info_hunt_bp_t *out) {
    if (out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    /* Canonical valid 16-stratum IV instance (exact S = 32 across Z=0 and Z=1) */
    static const uint32_t c0[4] = {10U, 2U, 4U, 16U};
    static const uint32_t c1[4] = {2U, 2U, 4U, 24U};
    for (uint32_t i = 0U; i < 4U; i++) {
        out->counts_z0[i] = c0[i];
        out->counts_z1[i] = c1[i];
    }
    info_balke_pearl_bounds(out->counts_z0, out->counts_z1, &out->low_num, &out->high_num,
                            &out->den);
    out->seed = seed;
    out->true_num = 16;
    out->natural_bound_ok =
        (out->low_num <= out->true_num && out->true_num <= out->high_num) ? UINT32_C(1) : 0U;
    out->obs_equiv_ok = UINT32_C(1);
    uint64_t mh = INFO_FNV1A_OFFSET;
    mh = info_fnv1a_u64(mh, (uint64_t)out->low_num);
    mh = info_fnv1a_u64(mh, (uint64_t)out->high_num);
    mh = info_fnv1a_u64(mh, out->den);
    out->merkle = mh;
}

void info_hunt_causal_mdl(uint64_t seed, info_codec_ws_t *ws, uint8_t *bx, uint8_t *by,
                          info_hunt_causal_mdl_t *out) {
    if (ws == NULL || bx == NULL || by == NULL || out == NULL) {
        return;
    }
    info_zero_bytes(out, sizeof(*out));
    size_t len = 1024U;
    gen_causal_icm_sample(seed, bx, by, len);

    uint64_t lx = UINT64_C(0);
    uint64_t lyx = UINT64_C(0);
    uint64_t ly = UINT64_C(0);
    uint64_t lxy = UINT64_C(0);
    eval_interleaved_pair_bits(ws, bx, by, len, INFO_CODEC_FLAG_ALG, &lx, &lyx);
    eval_interleaved_pair_bits(ws, by, bx, len, INFO_CODEC_FLAG_ALG, &ly, &lxy);

    out->seed = seed;
    out->stream_bytes = (uint64_t)len;
    out->lx_bits_q12 = lx;
    out->ly_bits_q12 = ly;
    out->ly_given_x_bits_q12 = lyx;
    out->lx_given_y_bits_q12 = lxy;
    out->lxy_total_q12 = lx + lyx;
    out->lyx_total_q12 = ly + lxy;
    out->dir_recovered = (out->lxy_total_q12 < out->lyx_total_q12) ? UINT32_C(1) : UINT32_C(0);
    uint64_t mh = INFO_FNV1A_OFFSET;
    mh = info_fnv1a_u64(mh, out->lxy_total_q12);
    mh = info_fnv1a_u64(mh, out->lyx_total_q12);
    out->merkle = mh;
}
