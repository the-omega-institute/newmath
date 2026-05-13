#ifndef GC_ENCODING_H
#define GC_ENCODING_H

#include <stddef.h>
#include <stdint.h>

typedef enum {
    GC_OK                          = 0,
    GC_REJECT_DANGLING_ONE         = 1,
    GC_REJECT_UNFINISHED_EVENT     = 2,
    GC_REJECT_NONBINARY_CHARACTER  = 3,
    GC_REJECT_EMPTY_INPUT_POLICY   = 4,
    GC_REJECT_RESOURCE_BOUND_EXCESS = 5,
    GC_REJECT_NONCANONICAL_DISPLAY = 6
} GcStatus;

/* Body encoding: b0 -> "0"; b1 -> "10". out_cap must be >= 2*in_len.
   Returns the number of bytes written. */
size_t gc_body_encode(const uint8_t *in, size_t in_len, uint8_t *out, size_t out_cap);

/* Event encoding: body_encode(in) ++ "11". out_cap must be >= 2*in_len + 2. */
size_t gc_event_encode(const uint8_t *in, size_t in_len, uint8_t *out, size_t out_cap);

/* Flow encoding: concat of event_encode for each event in a list.
   in[] is the flat list of events; event_lens[] gives each event length. */
size_t gc_flow_encode(uint8_t * const *events, const size_t *event_lens, size_t num_events,
                      uint8_t *out, size_t out_cap);

typedef struct {
    GcStatus status;
    uint8_t *event;           /* decoded event bytes; caller frees */
    size_t   event_len;
    size_t   bytes_consumed;  /* how many bytes of input were consumed */
} GcDecResult;

/* Decode a single event from input. fuel is max recursion depth (Lean DecodeFuel mirror).
   Returns GC_OK + filled event/event_len/bytes_consumed, or a reject status. */
GcDecResult gc_dec_event(const uint8_t *in, size_t in_len, size_t fuel);

/* BHist representation as a buffer of constructor choices.
 * Each byte is 0 (for e0) or 1 (for e1). Length = depth.
 * Empty is represented by length=0. */
typedef struct {
    uint8_t *choices;
    size_t   depth;
} BHist;

/* Encode a BHist as a bit stream using GroundCompiler convention.
 * Equivalent to EventEncoding(bhist->choices). */
size_t gc_bhist_encode(const BHist *bhist, uint8_t *out, size_t out_cap);

/* Decode a bit stream into a BHist. Caller must free out->choices.
 * Returns the same GcStatus values as gc_dec_event. */
typedef struct {
    GcStatus status;
    BHist    bhist;
    size_t   bytes_consumed;
} GcBhistDecResult;

GcBhistDecResult gc_bhist_decode(const uint8_t *in, size_t in_len, size_t fuel);

#endif
