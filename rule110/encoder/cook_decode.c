#include "cook_decode.h"
#include "cook_construction.h"
#include "glider_phases.h"

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define COOK_DECODE_MAX_C2_HITS 8192
#define COOK_DECODE_MAX_PACKETS 2048
#define COOK_DECODE_ETHER_WIDTH 14
#define COOK_DECODE_C2_COUNT 4
#define COOK_DECODE_REGION_GAP_CELLS 4096
#define COOK_DECODE_LEDGER_SLOT_WIDTH 65536
#define COOK_DECODE_LEDGER_PREFIX_SLOTS 3
#define COOK_DECODE_LEDGER_PHASE0 0
#define COOK_DECODE_LEDGER_PHASE_MARK 9
#define COOK_DECODE_LEDGER_PHASE_N 2
#define COOK_DECODE_LEDGER_PHASE_Y 5

typedef struct {
    size_t pos;
    int phase;
} C2Hit;

typedef struct {
    size_t pos;
    char symbol;
} CookPacket;

static int row_matches_bits(const uint8_t *row,
                            size_t len,
                            size_t pos,
                            const char *bits,
                            size_t bits_len) {
    if (row == NULL || bits == NULL) return 0;
    if (pos > len || bits_len > len - pos) return 0;
    for (size_t i = 0; i < bits_len; i++) {
        uint8_t want = (uint8_t)(bits[i] == '1');

        if ((row[pos + i] ? 1u : 0u) != want) return 0;
    }
    return 1;
}

static int phase_score_at(const uint8_t *row,
                          size_t len,
                          size_t pos,
                          int phase_offset) {
    size_t sample = 256;
    size_t start = pos +
        ((COOK_DECODE_LEDGER_SLOT_WIDTH - sample) / 2u);
    int score = 0;

    if (pos > len) return -1;
    if (start > len || sample > len - start) return -1;
    for (size_t i = 0; i < sample; i++) {
        uint8_t want =
            COOK_ETHER_PATTERN[(start + i + (size_t)phase_offset) %
                               (size_t)COOK_DECODE_ETHER_WIDTH];

        if ((row[start + i] ? 1u : 0u) == want) score++;
    }
    return score;
}

static int classify_ledger_slot(const uint8_t *row,
                                size_t len,
                                size_t pos,
                                int *phase_out) {
    int best_phase = 0;
    int best_score = -1;
    int second_score = -1;

    if (phase_out == NULL) return 0;
    if (pos > len || COOK_DECODE_LEDGER_SLOT_WIDTH > len - pos) return 0;
    for (int phase = 0; phase < COOK_DECODE_ETHER_WIDTH; phase++) {
        int score = phase_score_at(row, len, pos, phase);

        if (score > best_score) {
            second_score = best_score;
            best_score = score;
            best_phase = phase;
        } else if (score > second_score) {
            second_score = score;
        }
    }
    if (best_score < 220 || best_score - second_score < 40) return 0;
    *phase_out = best_phase;
    return 1;
}

static int decode_ledger_bit(const uint8_t *row,
                             size_t len,
                             size_t pos,
                             int base_phase,
                             uint8_t *bit_out) {
    int phase = 0;
    int rel = 0;

    if (bit_out == NULL || !classify_ledger_slot(row, len, pos, &phase)) {
        return 0;
    }
    rel = (phase - base_phase + COOK_DECODE_ETHER_WIDTH) %
        COOK_DECODE_ETHER_WIDTH;
    if (rel == COOK_DECODE_LEDGER_PHASE_N) {
        *bit_out = 0;
        return 1;
    }
    if (rel == COOK_DECODE_LEDGER_PHASE_Y) {
        *bit_out = 1;
        return 1;
    }
    return 0;
}

static int decode_phase_ledger(const uint8_t *row,
                               size_t len,
                               char *out_buf,
                               size_t buf_size) {
    size_t limit = 0;
    int found = 0;
    char best[COOK_DECODE_MAX_PACKETS];
    size_t best_len = 0;

    if (len < COOK_DECODE_LEDGER_PREFIX_SLOTS *
              (size_t)COOK_DECODE_LEDGER_SLOT_WIDTH) {
        return COOK_DECODE_NO_OUTPUT;
    }
    best[0] = '\0';
    limit = len -
        (COOK_DECODE_LEDGER_PREFIX_SLOTS *
         (size_t)COOK_DECODE_LEDGER_SLOT_WIDTH);
    for (size_t pos = 0;
         pos <= limit;
         pos += (size_t)COOK_DECODE_ETHER_WIDTH) {
        int phase = 0;
        int base_phase = 0;
        uint8_t bit = 0;
        size_t payload_len = 0;

        if (!classify_ledger_slot(row, len, pos, &phase) ||
            phase == COOK_DECODE_LEDGER_PHASE0) {
            continue;
        }
        base_phase = (phase - COOK_DECODE_LEDGER_PHASE_MARK +
                      COOK_DECODE_ETHER_WIDTH) %
            COOK_DECODE_ETHER_WIDTH;
        if (!decode_ledger_bit(row,
                               len,
                               pos + COOK_DECODE_LEDGER_SLOT_WIDTH,
                               base_phase,
                               &bit) ||
            bit != 0) {
            continue;
        }
        if (!classify_ledger_slot(row,
                                  len,
                                  pos + (2 * COOK_DECODE_LEDGER_SLOT_WIDTH),
                                  &phase) ||
            ((phase - base_phase + COOK_DECODE_ETHER_WIDTH) %
             COOK_DECODE_ETHER_WIDTH) != COOK_DECODE_LEDGER_PHASE_MARK) {
            continue;
        }
        for (size_t i = 0;
             pos + ((COOK_DECODE_LEDGER_PREFIX_SLOTS + i + 1) *
                    COOK_DECODE_LEDGER_SLOT_WIDTH) <= len &&
             i + 1 < sizeof(best);
             i++) {
            if (!decode_ledger_bit(row,
                                   len,
                                   pos + ((COOK_DECODE_LEDGER_PREFIX_SLOTS + i) *
                                          COOK_DECODE_LEDGER_SLOT_WIDTH),
                                   base_phase,
                                   &bit)) {
                break;
            }
            best[i] = bit ? 'Y' : 'N';
            payload_len = i + 1;
        }
        if (payload_len > 0 &&
            (!found || payload_len >= best_len)) {
            if (payload_len + 1 > buf_size) return COOK_DECODE_OUTPUT_TRUNCATED;
            best[payload_len] = '\0';
            best_len = payload_len;
            found = 1;
        }
    }
    if (!found) return COOK_DECODE_NO_OUTPUT;
    strcpy(out_buf, best);
    return COOK_DECODE_OK;
}

static int c2_phase_at(const uint8_t *row, size_t len, size_t pos) {
    for (int phase = 1; phase <= 4; phase++) {
        size_t phase_len = 0;
        const char *bits = glider_phase("C2", "A", phase, &phase_len);

        if (row_matches_bits(row, len, pos, bits, phase_len)) return phase;
    }
    return 0;
}

static size_t collect_c2_hits(const uint8_t *row,
                              size_t len,
                              C2Hit *hits,
                              size_t hit_cap) {
    size_t count = 0;

    for (size_t pos = 0; pos < len; pos++) {
        int phase = c2_phase_at(row, len, pos);

        if (phase == 0) continue;
        if (count < hit_cap) {
            hits[count].pos = pos;
            hits[count].phase = phase;
        }
        count++;
    }
    if (count > hit_cap) return hit_cap;
    return count;
}

static int has_hit_at(const C2Hit *hits, size_t hit_count, size_t pos) {
    for (size_t i = 0; i < hit_count; i++) {
        if (hits[i].pos == pos) return 1;
        if (hits[i].pos > pos) return 0;
    }
    return 0;
}

static size_t spacing_step(int spacing_tiles) {
    size_t c2_len = 0;

    (void)glider_phase("C2", "A", 1, &c2_len);
    return c2_len + ((size_t)spacing_tiles * (size_t)COOK_DECODE_ETHER_WIDTH);
}

static int packet_matches_at(const C2Hit *hits,
                             size_t hit_count,
                             size_t pos,
                             const int spacings[3]) {
    size_t cursor = pos;

    if (!has_hit_at(hits, hit_count, cursor)) return 0;
    for (size_t i = 0; i < COOK_DECODE_C2_COUNT - 1; i++) {
        cursor += spacing_step(spacings[i]);
        if (!has_hit_at(hits, hit_count, cursor)) return 0;
    }
    return 1;
}

static size_t collect_packets(const C2Hit *hits,
                              size_t hit_count,
                              CookPacket *packets,
                              size_t packet_cap) {
    static const int Y_SPACINGS[3] = {18, 18, 14};
    static const int N_SPACINGS[3] = {18, 10, 14};
    size_t count = 0;

    for (size_t i = 0; i < hit_count; i++) {
        char symbol = '\0';

        if (packet_matches_at(hits, hit_count, hits[i].pos, Y_SPACINGS)) {
            symbol = 'Y';
        } else if (packet_matches_at(hits, hit_count, hits[i].pos, N_SPACINGS)) {
            symbol = 'N';
        }
        if (symbol == '\0') continue;
        if (count < packet_cap) {
            packets[count].pos = hits[i].pos;
            packets[count].symbol = symbol;
        }
        count++;
    }
    if (count > packet_cap) return packet_cap;
    return count;
}

static void choose_packet_region(const CookPacket *packets,
                                 size_t packet_count,
                                 size_t *start_out,
                                 size_t *end_out) {
    size_t best_start = 0;
    size_t best_end = 1;
    size_t run_start = 0;

    for (size_t i = 1; i < packet_count; i++) {
        if (packets[i].pos - packets[i - 1].pos > COOK_DECODE_REGION_GAP_CELLS) {
            if (i - run_start > best_end - best_start) {
                best_start = run_start;
                best_end = i;
            }
            run_start = i;
        }
    }
    if (packet_count - run_start > best_end - best_start) {
        best_start = run_start;
        best_end = packet_count;
    }

    *start_out = best_start;
    *end_out = best_end;
}

int cook_decode_output(const uint8_t *evolved_row,
                       size_t len,
                       char *out_buf,
                       size_t buf_size) {
    C2Hit hits[COOK_DECODE_MAX_C2_HITS];
    CookPacket packets[COOK_DECODE_MAX_PACKETS];
    size_t hit_count = 0;
    size_t packet_count = 0;
    size_t region_start = 0;
    size_t region_end = 0;
    size_t out_len = 0;
    int ledger_rc = COOK_DECODE_NO_OUTPUT;

    if (out_buf != NULL && buf_size > 0) out_buf[0] = '\0';
    if (evolved_row == NULL || out_buf == NULL || buf_size == 0) {
        return COOK_DECODE_INVALID_INPUT;
    }

    ledger_rc = decode_phase_ledger(evolved_row, len, out_buf, buf_size);
    if (ledger_rc != COOK_DECODE_NO_OUTPUT) return ledger_rc;

    hit_count = collect_c2_hits(evolved_row,
                                len,
                                hits,
                                COOK_DECODE_MAX_C2_HITS);
    packet_count = collect_packets(hits,
                                   hit_count,
                                   packets,
                                   COOK_DECODE_MAX_PACKETS);
    if (packet_count == 0) return COOK_DECODE_NO_OUTPUT;

    choose_packet_region(packets, packet_count, &region_start, &region_end);
    out_len = region_end - region_start;
    if (out_len + 1 > buf_size) return COOK_DECODE_OUTPUT_TRUNCATED;

    for (size_t i = 0; i < out_len; i++) {
        out_buf[i] = packets[region_start + i].symbol;
    }
    out_buf[out_len] = '\0';
    return COOK_DECODE_OK;
}
