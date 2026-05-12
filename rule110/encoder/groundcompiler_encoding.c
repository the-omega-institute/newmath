#include "groundcompiler_encoding.h"
#include <stdlib.h>
#include <string.h>

size_t gc_body_encode(const uint8_t *in, size_t in_len, uint8_t *out, size_t out_cap) {
    size_t o = 0;
    for (size_t i = 0; i < in_len; i++) {
        if (in[i] == 0) {
            if (o + 1 > out_cap) return o;  /* underbuffer; partial -- caller's responsibility */
            out[o++] = 0;
        } else {
            if (o + 2 > out_cap) return o;
            out[o++] = 1;
            out[o++] = 0;
        }
    }
    return o;
}

size_t gc_event_encode(const uint8_t *in, size_t in_len, uint8_t *out, size_t out_cap) {
    size_t n = gc_body_encode(in, in_len, out, out_cap);
    if (n + 2 > out_cap) return n;
    out[n++] = 1;
    out[n++] = 1;
    return n;
}

size_t gc_flow_encode(uint8_t * const *events, const size_t *event_lens, size_t num_events,
                      uint8_t *out, size_t out_cap) {
    size_t total = 0;
    for (size_t i = 0; i < num_events; i++) {
        size_t written = gc_event_encode(events[i], event_lens[i], out + total, out_cap - total);
        total += written;
        if (total >= out_cap) break;
    }
    return total;
}

GcDecResult gc_dec_event(const uint8_t *in, size_t in_len, size_t fuel) {
    GcDecResult r = {GC_OK, NULL, 0, 0};
    if (in_len == 0 || in == NULL) { r.status = GC_REJECT_EMPTY_INPUT_POLICY; return r; }

    uint8_t *evt = (uint8_t *)malloc(in_len ? in_len : 1);
    if (!evt) { r.status = GC_REJECT_RESOURCE_BOUND_EXCESS; return r; }
    size_t eo = 0;
    size_t i = 0;
    size_t used_fuel = 0;

    while (i < in_len) {
        if (used_fuel >= fuel) {
            r.status = GC_REJECT_RESOURCE_BOUND_EXCESS; r.event = evt; r.event_len = eo;
            return r;
        }
        used_fuel++;

        if (in[i] == 0) {
            evt[eo++] = 0;
            i++;
        } else if (in[i] == 1) {
            if (i + 1 >= in_len) {
                /* "1" at end of input with no following byte */
                r.status = GC_REJECT_DANGLING_ONE; r.event = evt; r.event_len = eo;
                return r;
            }
            if (in[i + 1] == 0) {
                evt[eo++] = 1;
                i += 2;
            } else /* in[i+1] == 1 */ {
                /* Terminator. */
                r.status = GC_OK;
                r.event = evt;
                r.event_len = eo;
                r.bytes_consumed = i + 2;
                return r;
            }
        } else {
            /* Should not happen; input bytes are bits. */
            r.status = GC_REJECT_NONBINARY_CHARACTER; r.event = evt; r.event_len = eo;
            return r;
        }
    }
    /* Ran out of input with no terminator. */
    r.status = GC_REJECT_UNFINISHED_EVENT; r.event = evt; r.event_len = eo;
    return r;
}
