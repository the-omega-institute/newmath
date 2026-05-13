# BHist Encoding

`BHist` is the closed inductive history type

```text
Empty | e0 BHist | e1 BHist
```

Unlike `BMark`, which has exactly two values, `BHist` is countably infinite:
each constructor layer adds one choice before the final `Empty`.

The ground encoding views a `BHist` as the finite sequence of constructor
choices seen from the outside inward:

```text
Empty                 -> []
e0 h                  -> 0 :: choices(h)
e1 h                  -> 1 :: choices(h)
```

The byte representation is therefore a buffer of `0` and `1` values, with
length equal to history depth. `Empty` has depth `0`.

The bit-stream representation reuses the GroundCompiler `EventEncoding`
without a second format. The choice sequence is encoded as the event payload:

```text
BHistEncoding(h) = EventEncoding(choices(h))
```

The body convention remains `0 -> "0"` and `1 -> "10"`, followed by the event
terminator `"11"`. The terminator is exactly where the `Empty` constructor is
reached.

Decoding is the inverse operation:

1. Run `gc_dec_event` on the input stream.
2. Interpret the decoded event bytes as constructor choices.
3. Rebuild the history by reading choices left to right, ending in `Empty`.

Examples:

```text
Empty                                  choices []             -> "11"
e0 Empty                               choices [0]            -> "011"
e1 Empty                               choices [1]            -> "1011"
e0 (e1 Empty)                          choices [0,1]          -> "01011"
e0 (e1 (e0 (e1 (e1 Empty))))           choices [0,1,0,1,1]    -> "0100101011"
```

This uses option alpha: reuse `EventEncoding` directly. A bespoke BHist
terminator would duplicate an existing delimiter and would make BHist streams
incompatible with the current event decoder. Reusing events keeps one
canonical stream grammar: the first `"11"` marks the end of the constructor
sequence, and event-level reject statuses remain the decoder contract.

Maximum depth is implementation-limited by the caller-provided decoder `fuel`.
The test suite uses small values for ordinary histories and larger values for
deep histories such as depth `100`; production callers should pass fuel at
least as large as the maximum accepted depth, with `8192` a reasonable default
for deep BHist payloads.
