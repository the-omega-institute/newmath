# Cook Output Decode Design

`cook_decode_output` is the observation layer for `.algo.r110.ct` rows. It does
not change Rule 110 evolution. It reads one evolved row and tries to recover the
cyclic-tag tape encoded by Cook C2 packets.

The implemented reader uses the phase catalog already used by the encoder:

- scan the row for `C2(A, phase)` signatures,
- recognize four-C2 packets with Cook section 4.3 spacings,
- map `18,18,14` to `Y` and `28,10,14` to `N`,
- choose the largest contiguous packet cluster as the tape-data window.

The `.algo.ct` reference tape is binary, so the semantic test maps `1` to `Y`
and `0` to `N` before comparison.

Current obstruction: the shipped `hsame_refl.algo.r110.ct` manifest evolves the
packet row for 128 Rule 110 steps. Diagnostic replay is stable, but the evolved
row does not currently expose a full C2 packet stream matching the CT final tape.
The decoder reports this mismatch instead of treating packet evolution as a
semantic round trip.

For the five `hsame_refl` cases, the initial rows expose 4, 6, 8, 10, and 14
valid packet starts, matching the input tape lengths. After 128 steps, the rows
still contain C2 phase fragments, but no complete four-C2 packet with either
Cook spacing tuple is present. The semantic target therefore fails at output
window extraction.

This narrows the open work to one of two points:

- choose the correct later observation row where the data band has settled into
  readable C2 packets, or
- extend the phase catalog/window search to the post-collision C2 phase family
  visible at that observation time.
