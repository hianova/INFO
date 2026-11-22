#include "info.h"

#include <stdio.h>

#define INFO_DECOMP_MAX_BYTES (4U * 1024U * 1024U)

static info_codec_ws_t g_decomp_ws;
static uint8_t g_in_buf[INFO_DECOMP_MAX_BYTES + 1024U];
static uint8_t g_out_buf[INFO_DECOMP_MAX_BYTES];

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
    size_t in_len = fread(g_in_buf, 1U, sizeof(g_in_buf), fi);
    (void)fclose(fi);
    if (in_len == 0U || in_len == sizeof(g_in_buf)) {
        (void)fprintf(stderr, "ERROR: invalid or oversized compressed stream\n");
        return 1;
    }

    size_t out_len = info_decompress(&g_decomp_ws, g_in_buf, in_len, g_out_buf, sizeof(g_out_buf));
    if (out_len == SIZE_MAX) {
        (void)fprintf(stderr, "ERROR: decompression failed (magic/hash/bounds)\n");
        return 1;
    }

    FILE *fo = fopen(argv[2], "wb");
    if (fo == NULL) {
        (void)fprintf(stderr, "ERROR: cannot write %s\n", argv[2]);
        return 1;
    }
    if (out_len > 0U && fwrite(g_out_buf, 1U, out_len, fo) != out_len) {
        (void)fclose(fo);
        return 1;
    }
    if (fclose(fo) != 0) {
        return 1;
    }
    return 0;
}
