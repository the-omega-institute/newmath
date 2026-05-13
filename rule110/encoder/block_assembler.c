#include "block_assembler.h"

#include "cook_blocks.h"

#include <stdlib.h>
#include <string.h>

void cook_block_string_init(CookBlockString *s) {
    s->data = NULL;
    s->len = 0;
    s->cap = 0;
    s->count = 0;
}

void cook_block_string_free(CookBlockString *s) {
    free(s->data);
    cook_block_string_init(s);
}

static int reserve_block_string(CookBlockString *s, size_t need) {
    char *next;
    size_t next_cap;

    if (need <= s->cap) return 1;
    next_cap = s->cap == 0 ? 64 : s->cap;
    while (next_cap < need) next_cap *= 2;
    next = (char *)realloc(s->data, next_cap);
    if (next == NULL) return 0;
    s->data = next;
    s->cap = next_cap;
    return 1;
}

int cook_block_string_append(CookBlockString *s, char symbol) {
    size_t add = s->len == 0 ? 1 : 2;

    if (cook_block_by_symbol(symbol) == NULL) return 0;
    if (!reserve_block_string(s, s->len + add + 1)) return 0;
    if (s->len != 0) s->data[s->len++] = ' ';
    s->data[s->len++] = symbol;
    s->data[s->len] = '\0';
    s->count++;
    return 1;
}

int cook_count_appendants(const uint8_t *const *productions,
                          const size_t *prod_lens,
                          size_t production_count,
                          CookAppenderStats *out) {
    size_t i;

    if (out == NULL) return 0;
    out->ys = 0;
    out->ns = 0;
    out->nonempty = 0;
    out->empty = 0;

    for (i = 0; i < production_count; i++) {
        size_t j;

        if (prod_lens[i] == 0) {
            out->empty++;
            continue;
        }
        out->nonempty++;
        for (j = 0; j < prod_lens[i]; j++) {
            if (productions[i][j] == 1) {
                out->ys++;
            } else if (productions[i][j] == 0) {
                out->ns++;
            } else {
                return 0;
            }
        }
    }
    return 1;
}

size_t cook_left_v_from_stats(const CookAppenderStats *stats) {
    return 76 * stats->ys +
           80 * stats->ns +
           60 * stats->nonempty +
           43 * stats->empty;
}

int cook_write_left_periodic(FILE *out, size_t left_v) {
    return fprintf(out,
                   "LEFT_PERIODIC_BLOCKS A^%zu B A^13 B A^11 B A^12 B\n",
                   left_v) > 0;
}

int cook_assemble_central_from_bits(const uint8_t *bits,
                                    size_t bits_len,
                                    CookBlockString *out) {
    size_t i;

    if (!cook_block_string_append(out, 'C')) return 0;
    if (bits_len == 0) return cook_block_string_append(out, 'G');

    for (i = 0; i < bits_len; i++) {
        if (bits[i] == 1) {
            if (!cook_block_string_append(out, 'F')) return 0;
        } else if (bits[i] == 0) {
            if (!cook_block_string_append(out, 'E')) return 0;
        } else {
            return 0;
        }
        if (!cook_block_string_append(out, i + 1 == bits_len ? 'G' : 'D')) {
            return 0;
        }
    }
    return 1;
}

int cook_assemble_right(const uint8_t *const *productions,
                        const size_t *prod_lens,
                        size_t production_count,
                        CookBlockString *out) {
    size_t i;

    for (i = 0; i < production_count; i++) {
        size_t j;

        if (prod_lens[i] == 0) {
            if (!cook_block_string_append(out, 'L')) return 0;
            continue;
        }
        for (j = 0; j < prod_lens[i]; j++) {
            if (j == 0) {
                if (!cook_block_string_append(out, 'K') ||
                    !cook_block_string_append(out, 'H')) {
                    return 0;
                }
            } else if (!cook_block_string_append(out, 'I')) {
                return 0;
            }

            if (productions[i][j] == 1) {
                if (!cook_block_string_append(out, 'I')) return 0;
            } else if (productions[i][j] == 0) {
                if (!cook_block_string_append(out, 'J')) return 0;
            } else {
                return 0;
            }
        }
    }
    return 1;
}

static const char *central_code(char symbol) {
    switch (symbol) {
    case 'C': return "0010";
    case 'D': return "0011";
    case 'E': return "0100";
    case 'F': return "0101";
    case 'G': return "0110";
    default: return NULL;
    }
}

int cook_central_bits_from_blocks(const CookBlockString *blocks,
                                  char **bits_out,
                                  size_t *bits_len_out) {
    char *bits;
    const char *p;
    size_t pos = 0;
    size_t out_len;

    if (blocks == NULL || bits_out == NULL || bits_len_out == NULL) return 0;
    out_len = blocks->count * 4;
    bits = (char *)malloc(out_len + 1);
    if (bits == NULL) return 0;

    for (p = blocks->data; p != NULL && *p != '\0'; p++) {
        const char *code;

        if (*p == ' ') continue;
        code = central_code(*p);
        if (code == NULL) {
            free(bits);
            return 0;
        }
        memcpy(bits + pos, code, 4);
        pos += 4;
    }
    bits[pos] = '\0';
    *bits_out = bits;
    *bits_len_out = pos;
    return pos == out_len;
}

static char *trim_ascii_local(char *s) {
    char *end;

    while (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r') s++;
    end = s + strlen(s);
    while (end > s &&
           (end[-1] == ' ' || end[-1] == '\t' ||
            end[-1] == '\n' || end[-1] == '\r')) {
        end--;
    }
    *end = '\0';
    return s;
}

static int parse_size_local(const char *s, size_t *out) {
    char *end = NULL;
    unsigned long value = strtoul(s, &end, 10);

    if (end == s) return 0;
    while (*end == ' ' || *end == '\t' || *end == '\n' || *end == '\r') end++;
    if (*end != '\0') return 0;
    *out = (size_t)value;
    return 1;
}

static int parse_bits_line(const char *line, uint8_t **out, size_t *len_out) {
    uint8_t *bits;
    size_t len = strlen(line);
    size_t i;

    bits = (uint8_t *)malloc(len ? len : 1);
    if (bits == NULL) return 0;
    for (i = 0; i < len; i++) {
        if (line[i] != '0' && line[i] != '1') {
            free(bits);
            return 0;
        }
        bits[i] = (uint8_t)(line[i] == '1');
    }
    *out = bits;
    *len_out = len;
    return 1;
}

int cook_scan_appendants_file(const char *path,
                              CookAppenderStats *stats,
                              CookBlockString *right) {
    FILE *f = fopen(path, "r");
    char line_buf[4096];
    uint8_t **productions = NULL;
    size_t *prod_lens = NULL;
    size_t count = 0;
    size_t index = 0;
    int ok = 0;

    if (f == NULL && strncmp(path, "rule110/", 8) == 0) f = fopen(path + 8, "r");
    if (f == NULL) return 0;
    while (fgets(line_buf, sizeof(line_buf), f) != NULL) {
        char *line = trim_ascii_local(line_buf);

        if (line[0] == '\0' || line[0] == '#') continue;
        if (count != 0 && index < count) {
            if (!parse_bits_line(line, &productions[index], &prod_lens[index])) {
                goto done;
            }
            index++;
            continue;
        }
        if (strncmp(line, "PRODUCTIONS ", 12) == 0) {
            if (!parse_size_local(line + 12, &count)) goto done;
            productions =
                (uint8_t **)calloc(count ? count : 1, sizeof(uint8_t *));
            prod_lens = (size_t *)calloc(count ? count : 1, sizeof(size_t));
            if (productions == NULL || prod_lens == NULL) goto done;
        } else if (strncmp(line, "ASSERTIONS ", 11) == 0) {
            break;
        }
    }
    if (index != count) goto done;
    ok = cook_count_appendants((const uint8_t *const *)productions,
                               prod_lens,
                               count,
                               stats) &&
         cook_assemble_right((const uint8_t *const *)productions,
                             prod_lens,
                             count,
                             right);

done:
    if (productions != NULL) {
        size_t i;

        for (i = 0; i < count; i++) free(productions[i]);
    }
    free(productions);
    free(prod_lens);
    fclose(f);
    return ok;
}

static int input_to_bits(const char *input, uint8_t **out, size_t *len_out) {
    return parse_bits_line(input, out, len_out);
}

int cook_validate_symbolic_case(const char *input,
                                const char *left_blocks,
                                size_t left_v,
                                size_t expected_left_v,
                                const char *central_blocks,
                                const char *central_bits,
                                const char *right_blocks,
                                size_t right_count,
                                const CookBlockString *expected_right) {
    uint8_t *input_bits = NULL;
    char *expected_central_bits = NULL;
    size_t input_len = 0;
    size_t central_bits_len = 0;
    char expected_left[128];
    CookBlockString expected_central;
    int ok = 0;

    cook_block_string_init(&expected_central);
    if (!input_to_bits(input, &input_bits, &input_len)) goto done;
    if (!cook_assemble_central_from_bits(input_bits,
                                         input_len,
                                         &expected_central)) {
        goto done;
    }
    if (!cook_central_bits_from_blocks(&expected_central,
                                       &expected_central_bits,
                                       &central_bits_len)) {
        goto done;
    }
    if (central_bits_len >= 100000) goto done;
    snprintf(expected_left,
             sizeof(expected_left),
             "A^%zu B A^13 B A^11 B A^12 B",
             expected_left_v);
    ok = left_v == expected_left_v &&
         strcmp(left_blocks, expected_left) == 0 &&
         strcmp(central_blocks,
                expected_central.data != NULL ? expected_central.data : "") == 0 &&
         strlen(central_bits) == central_bits_len &&
         strcmp(central_bits, expected_central_bits) == 0 &&
         strcmp(right_blocks,
                expected_right->data != NULL ? expected_right->data : "") == 0 &&
         right_count == expected_right->count;

done:
    free(input_bits);
    free(expected_central_bits);
    cook_block_string_free(&expected_central);
    return ok;
}

static int read_line_local(FILE *f, char *buf, size_t cap) {
    char *line;

    if (fgets(buf, (int)cap, f) == NULL) return 0;
    line = trim_ascii_local(buf);
    if (line != buf) memmove(buf, line, strlen(line) + 1);
    return 1;
}

static int parse_prefixed_text_local(const char *line,
                                     const char *prefix,
                                     char *out,
                                     size_t out_cap) {
    size_t prefix_len = strlen(prefix);
    size_t len;

    if (strncmp(line, prefix, prefix_len) != 0) return 0;
    len = strlen(line + prefix_len);
    if (len + 1 > out_cap) return 0;
    memcpy(out, line + prefix_len, len + 1);
    return 1;
}

static int parse_case_input_local(char *line,
                                  char *name,
                                  size_t name_cap,
                                  char *input,
                                  size_t input_cap) {
    char *cursor = trim_ascii_local(line);
    char *colon;
    char *field;

    if (strncmp(cursor, "case ", 5) != 0) return 0;
    cursor += 5;
    colon = strchr(cursor, ':');
    if (colon == NULL) return 0;
    *colon = '\0';
    if (strlen(trim_ascii_local(cursor)) + 1 > name_cap) return 0;
    strcpy(name, trim_ascii_local(cursor));
    field = colon + 1;
    while (*field != '\0') {
        char *semi = strchr(field, ';');
        char *eq;
        char *key;
        char *value;

        if (semi != NULL) *semi = '\0';
        field = trim_ascii_local(field);
        eq = strchr(field, '=');
        if (eq != NULL) {
            *eq = '\0';
            key = trim_ascii_local(field);
            value = trim_ascii_local(eq + 1);
            if (strcmp(key, "input") == 0) {
                if (strcmp(value, "<empty>") == 0) value = "";
                if (strlen(value) + 1 > input_cap) return 0;
                strcpy(input, value);
                return 1;
            }
        }
        if (semi == NULL) break;
        field = semi + 1;
    }
    return 0;
}

static int is_binary_local(const char *s) {
    size_t i;

    for (i = 0; s[i] != '\0'; i++) {
        if (s[i] != '0' && s[i] != '1') return 0;
    }
    return 1;
}

int cook_read_validate_symbolic_case(FILE *f,
                                     const char *case_line,
                                     size_t expected_left_v,
                                     const CookBlockString *expected_right) {
    char line[65536];
    char input[2048];
    char left[128];
    char central[4096];
    char central_bits[16384];
    char right[65536];
    size_t left_v = 0;
    size_t right_count = 0;

    if (strncmp(case_line, "case ", 5) != 0) return 0;
    if (!read_line_local(f, line, sizeof(line)) ||
        !parse_prefixed_text_local(line, "INPUT ", input, sizeof(input))) {
        return 0;
    }
    if (!read_line_local(f, line, sizeof(line)) ||
        !parse_prefixed_text_local(line,
                                   "LEFT_PERIODIC_BLOCKS ",
                                   left,
                                   sizeof(left))) {
        return 0;
    }
    if (!read_line_local(f, line, sizeof(line)) ||
        strncmp(line, "LEFT_V ", 7) != 0 ||
        !parse_size_local(line + 7, &left_v)) {
        return 0;
    }
    if (!read_line_local(f, line, sizeof(line)) ||
        !parse_prefixed_text_local(line,
                                   "CENTRAL_BLOCKS ",
                                   central,
                                   sizeof(central))) {
        return 0;
    }
    if (!read_line_local(f, line, sizeof(line)) ||
        !parse_prefixed_text_local(line,
                                   "CENTRAL_BITS ",
                                   central_bits,
                                   sizeof(central_bits))) {
        return 0;
    }
    if (!read_line_local(f, line, sizeof(line)) ||
        !parse_prefixed_text_local(line,
                                   "RIGHT_PERIODIC_BLOCKS ",
                                   right,
                                   sizeof(right))) {
        return 0;
    }
    if (!read_line_local(f, line, sizeof(line)) ||
        strncmp(line, "RIGHT_BLOCK_COUNT ", 18) != 0 ||
        !parse_size_local(line + 18, &right_count)) {
        return 0;
    }
    return cook_validate_symbolic_case(input,
                                       left,
                                       left_v,
                                       expected_left_v,
                                       central,
                                       central_bits,
                                       right,
                                       right_count,
                                       expected_right);
}

int cook_source_binary_direct_count(const char *path,
                                    size_t *count_out) {
    FILE *f = fopen(path, "r");
    char line[4096];
    size_t count = 0;

    if (f == NULL && strncmp(path, "rule110/", 8) == 0) f = fopen(path + 8, "r");
    if (f == NULL || count_out == NULL) return 0;
    while (fgets(line, sizeof(line), f) != NULL) {
        char name[128];
        char input[2048];

        if (parse_case_input_local(line, name, sizeof(name), input, sizeof(input))) {
            if (is_binary_local(input)) count++;
        }
    }
    fclose(f);
    *count_out = count;
    return 1;
}

int cook_source_case_input_matches(const char *path,
                                   const char *name,
                                   const char *input) {
    FILE *f = fopen(path, "r");
    char line[4096];
    int found = 0;

    if (f == NULL && strncmp(path, "rule110/", 8) == 0) f = fopen(path + 8, "r");
    if (f == NULL) return 0;
    while (fgets(line, sizeof(line), f) != NULL) {
        char got_name[128];
        char got_input[2048];

        if (parse_case_input_local(line,
                                   got_name,
                                   sizeof(got_name),
                                   got_input,
                                   sizeof(got_input)) &&
            strcmp(got_name, name) == 0) {
            found = strcmp(got_input, input) == 0;
            break;
        }
    }
    fclose(f);
    return found;
}
