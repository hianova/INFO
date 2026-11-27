#include "info.h"

#include <stdio.h>

#define INFO_DECOMP_MAX_BYTES (4U * 1024U * 1024U)

static info_codec_ws_t g_decomp_ws;
static info_hutter_ws_t g_hutter_ws;
static info_hutter_state_t g_hutter_st;
static uint8_t g_in_buf[INFO_DECOMP_MAX_BYTES + 1024U];
static uint8_t g_out_buf[INFO_DECOMP_MAX_BYTES];

static uint32_t decomp_get_u32_le(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8U) | ((uint32_t)p[2] << 16U) |
           ((uint32_t)p[3] << 24U);
}

static int decomp_inf1(FILE *fi, FILE *fo, const uint8_t magic_hdr[4]) {
    g_in_buf[0] = magic_hdr[0];
    g_in_buf[1] = magic_hdr[1];
    g_in_buf[2] = magic_hdr[2];
    g_in_buf[3] = magic_hdr[3];
    size_t rest = fread(g_in_buf + 4U, 1U, sizeof(g_in_buf) - 4U, fi);
    size_t in_len = 4U + rest;
    if (in_len < INFO_INF1_HEADER_BYTES || in_len == sizeof(g_in_buf)) {
        (void)fprintf(stderr, "ERROR: invalid or oversized compressed stream\n");
        return 1;
    }
    size_t out_len = info_decompress(&g_decomp_ws, g_in_buf, in_len, g_out_buf, sizeof(g_out_buf));
    if (out_len == SIZE_MAX) {
        (void)fprintf(stderr, "ERROR: decompression failed (magic/hash/bounds)\n");
        return 1;
    }
    if (out_len > 0U && fwrite(g_out_buf, 1U, out_len, fo) != out_len) {
        return 1;
    }
    return 0;
}

static int decomp_inf2(FILE *fi, FILE *fo, const uint8_t magic_hdr[4]) {
    uint8_t hdr[INFO_INF2_HEADER_BYTES];
    hdr[0] = magic_hdr[0];
    hdr[1] = magic_hdr[1];
    hdr[2] = magic_hdr[2];
    hdr[3] = magic_hdr[3];
    if (fread(hdr + 4U, 1U, INFO_INF2_HEADER_BYTES - 4U, fi) !=
        (size_t)(INFO_INF2_HEADER_BYTES - 4U)) {
        (void)fprintf(stderr, "ERROR: truncated INF2 header\n");
        return 1;
    }
    uint32_t flags = UINT32_C(0);
    uint64_t orig_bytes = UINT64_C(0);
    if (!info_inf2_parse_header(hdr, &flags, &orig_bytes)) {
        (void)fprintf(stderr, "ERROR: invalid INF2 header\n");
        return 1;
    }

    info_hutter_stream_begin(&g_hutter_ws, &g_hutter_st, flags);
    uint64_t decoded = UINT64_C(0);
    while (decoded < orig_bytes) {
        uint8_t bhdr[INFO_INF2_BLOCK_HDR];
        if (fread(bhdr, 1U, INFO_INF2_BLOCK_HDR, fi) != (size_t)INFO_INF2_BLOCK_HDR) {
            (void)fprintf(stderr, "ERROR: truncated INF2 block header\n");
            return 1;
        }
        uint32_t raw_len = UINT32_C(0);
        uint32_t cmp_len = UINT32_C(0);
        info_inf2_parse_block_hdr(bhdr, &raw_len, &cmp_len);
        if (raw_len == 0U || raw_len > INFO_INF2_BLOCK_MAX ||
            (uint64_t)raw_len > (orig_bytes - decoded) || cmp_len == 0U ||
            (size_t)cmp_len > sizeof(g_in_buf)) {
            (void)fprintf(stderr, "ERROR: invalid INF2 block bounds\n");
            return 1;
        }
        if (fread(g_in_buf, 1U, (size_t)cmp_len, fi) != (size_t)cmp_len) {
            (void)fprintf(stderr, "ERROR: truncated INF2 block payload\n");
            return 1;
        }
        size_t got = info_hutter_decode_block(&g_hutter_ws, &g_hutter_st, g_in_buf, (size_t)cmp_len,
                                              g_out_buf, (size_t)raw_len);
        if (got != (size_t)raw_len) {
            (void)fprintf(stderr, "ERROR: INF2 block decode failed\n");
            return 1;
        }
        if (fwrite(g_out_buf, 1U, (size_t)raw_len, fo) != (size_t)raw_len) {
            return 1;
        }
        decoded += (uint64_t)raw_len;
    }

    uint8_t tr[INFO_INF2_TRAILER_BYTES];
    if (fread(tr, 1U, INFO_INF2_TRAILER_BYTES, fi) != (size_t)INFO_INF2_TRAILER_BYTES) {
        (void)fprintf(stderr, "ERROR: missing INF2 trailer\n");
        return 1;
    }
    uint64_t exp_fnv64 = info_get_u64_le_pub(tr);
    if (exp_fnv64 != info_hutter_stream_fnv64(&g_hutter_st) || fgetc(fi) != EOF) {
        (void)fprintf(stderr, "ERROR: INF2 checksum or trailing garbage mismatch\n");
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) {
        (void)fprintf(stderr, "Usage: info_decomp <in.inf> <out>\n");
        return 1;
    }
    FILE *fi = fopen(argv[1], "rb");
    if (fi == NULL) {
        (void)fprintf(stderr, "ERROR: cannot open %s\n", argv[1]);
        return 1;
    }
    uint8_t magic_hdr[4];
    if (fread(magic_hdr, 1U, 4U, fi) != 4U) {
        (void)fclose(fi);
        (void)fprintf(stderr, "ERROR: empty or invalid compressed file\n");
        return 1;
    }
    FILE *fo = fopen(argv[2], "wb");
    if (fo == NULL) {
        (void)fclose(fi);
        (void)fprintf(stderr, "ERROR: cannot write %s\n", argv[2]);
        return 1;
    }

    uint32_t magic = decomp_get_u32_le(magic_hdr);
    int rc = 1;
    if (magic == INFO_INF1_MAGIC) {
        rc = decomp_inf1(fi, fo, magic_hdr);
    } else if (magic == INFO_INF2_MAGIC) {
        rc = decomp_inf2(fi, fo, magic_hdr);
    } else {
        (void)fprintf(stderr, "ERROR: unknown magic header\n");
    }

    (void)fclose(fi);
    if (fclose(fo) != 0) {
        return 1;
    }
    return rc;
}
