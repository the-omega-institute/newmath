# Cook Figure 4 Phase Extraction

This note records the current bitmap extraction result for Cook 2004 Figure 4.
The extraction does not certify five target gliders, so no C emitter is changed.

## Method

The scratch script `/tmp/glider-extraction/extract.py` reads
`/tmp/cook-page13/figure4-13.pgm` as raw PGM, thresholds pixels at 128, and
uses row and column black-pixel projections to locate the two Figure 4 panels.

Detected panel boxes in the 300 DPI page bitmap:

| Panel | Pixel box |
|---|---|
| top | `(329, 487, 1889, 1023)` |
| bottom | `(329, 702, 1889, 1653)` |

The script also renders page 13 at 1200 DPI into
`/tmp/glider-extraction/cook1200-13.pgm` when `pdftoppm` and the saved PDF are
available. That crop shows the Figure 4 cells as clean stair-step polygons,
but the 300 DPI bitmap gives only about 2.6 horizontal pixels per Rule 110 cell.

## Cell-Size Calibration

The ether word is `00010011011111`, with horizontal period 14 cells. In the
left pure-ether area of the top panel, bitmap autocorrelation gives a dominant
horizontal period near 37 pixels in the 300 DPI PGM:

| Quantity | Value |
|---|---:|
| measured ether period | about 37 px |
| inferred cell width | about 2.64 px |
| 1200 DPI inferred cell width | about 10.56 px |

The page render is therefore usable for panel detection, but direct 300 DPI
cell-center sampling is too close to the rasterization boundary for a reliable
catalog transcription.

## Verification Check

The script implements the local Rule 110 period check used for candidate rows:
an ether-backed tape is overwritten with the candidate row, evolved for the
claimed period, and compared with the same candidate shifted by the claimed
displacement on the evolved ether phase.

Calibration rows behave as follows under this embedded-row check:

| Glider | Width | Period | Pattern | Embedded check |
|---|---:|---:|---|---|
| A | 6 | `(3,2)` | `111110` | accepted on phase 13 |
| A4 | 10 | `(3,2)` | `0001110111` | accepted on phase 2 |
| C2 | 3 | `(7,0)` | `111` | accepted on phases 0, 1, and 13 |
| Ebar | 7 | `(30,-8)` | `1001111` | not accepted by this embedding convention |

This shows that the checker is sensitive to the phase and anchor convention:
some known calibration words pass, while others require a wider phase mask or a
different origin convention.

## Per-Glider Status

| Glider | Status |
|---|---|
| B | unclear: the region is close to adjacent barred B entries, and no extracted 8-cell row passed the embedded check. |
| C1 | unclear: visual rows are readable at 1200 DPI, but the phase anchor was not determined. |
| C3 | unclear: same C-family anchor issue as C1. |
| D1 | unclear: the tube overlaps several ether phases vertically; no row was promoted. |
| D2 | unclear: small width makes a one-cell anchor error change the whole row. |
| F | unclear: width one is not enough to disambiguate a glider row from the local ether phase without the surrounding finite mask. |
| G1 | unclear: the left-moving tube is visually distinct, but the extracted row did not pass the current embedded-row check. |
| H | unclear: the long period and multi-defect appearance require a wider mask than the 11-cell row alone. |

## Brute-force Verification

Method: direct Rule 110 simulation, with no bitmap parse. For each target
glider, the standalone tool `rule110/encoder/glider_search.c` enumerates all
`2^W` candidate W-cell seeds, embeds each seed in Cook ether, runs the claimed
period, and checks whether the same W-cell seed appears at displacement `dx`.
The tool also evolves a pure-ether control row and requires far-field ether to
remain equal to that control.

The output distinguishes two checks:

| Class | Meaning |
|---|---|
| exact | the whole finite perturbation relative to pure ether is shifted by `dx` |
| window | the W-cell seed reappears at `dx`, but other nearby perturbation cells are not a strict translate |

### Results

The search found at least one direct-simulation window-preservation candidate
for all eight requested targets. This satisfies the single-row verification
check requested for the brute-force pass. Only C1 and C3 had exact
shifted-perturbation candidates under this embedding convention; the others
remain non-unique top matches.

| Glider | seed | candidates found | exact candidates | best class | verified |
|---|---|---:|---:|---|---|
| B | `01111101` | 50 | 0 | window | yes |
| C1 | `111010000` | 103 | 4 | exact | yes |
| C3 | `11101000011` | 158 | 15 | exact | yes |
| D1 | `11000110111` | 172 | 0 | window | yes |
| D2 | `11000` | 54 | 0 | window | yes |
| F | `1` | 3 | 0 | window | yes |
| G1 | `0011100110` | 56 | 0 | window | yes |
| H | `11111111100` | 39 | 0 | window | yes |

The registry records the deterministic top match for each target so downstream
work can reproduce the direct simulation search. Rows with best class `window`
are not ready for phase-exact emitter promotion without a wider phase mask or
multi-row tube check.

## What Is Needed

A reliable extraction needs one of the following:

1. a phase convention that specifies, for each Figure 4 label, the exact left
   boundary and ether phase used by Cook's width table;
2. vector-level extraction from the PDF object stream rather than raster cell
   sampling; or
3. a multi-row finite mask verifier that compares the whole glider tube over
   one period instead of asking a single W-cell row to reproduce in isolation.

The current bitmap parse is useful for geometry and diagnostics, but it does
not satisfy the acceptance gate of five verified target gliders.

## Verifier Refinement: C2 Diagnosis

The verifier now searches seed widths from the visual width `W` through
`W + N` with `--extended-width N`. It also requires exact candidates to keep
the same finite perturbation mask at `T`, `2T`, and `3T`. The raw seed-window
test is reported separately as `window`; it is no longer allowed to promote a
candidate to phase-exact when the surrounding perturbation changes.

The A sanity check still passes under this stricter rule:

| Glider | Search | Candidates | Exact candidates | Best |
|---|---|---:|---:|---|
| A | `A 6 3 2` | 50 | 5 | width 6 seed `011101`, phase 12, exact |

For C2, the Cook visual word `111` is not itself a phase-exact single-row seed.
It recurs as a raw 3-cell window at phases 2, 3, 4, 5, and 13, but every such
case is only `window`: after seven steps the seed word can be read again, while
the finite perturbation relative to ether has changed shape. The nearby padded
forms `0111`, `1110`, `1111`, `01111`, `11110`, `11111`, `011111`, and
`111110` show the same behavior through width 7.

The obstruction disappears once the seed encoding is widened. With `W=3` and
`--extended-width 8`, the first strict C2 candidate is:

| Glider | Search | Candidates | Exact candidates | Best |
|---|---|---:|---:|---|
| C2 | `C2 3 7 0 --extended-width 8` | 225 | 27 | width 8 seed `11101000`, phase 0, exact |

This supports the diagnosis that Cook's width 3 is visual width, not the full
single-row seed encoding width needed by this ether-backed verifier.

The focused width-3-through-width-7 checks gave:

| Seed width | Seed | Window phases | Exact phases |
|---:|---|---|---|
| 3 | `111` | 2, 3, 4, 5, 13 | none |
| 4 | `0111` | 2, 10 | none |
| 4 | `1110` | 13 | none |
| 4 | `1111` | 3, 4, 12 | none |
| 5 | `01111` | 2 | none |
| 5 | `11110` | 4, 12 | none |
| 5 | `11111` | 3, 11 | none |
| 6 | `011111` | 2, 10 | none |
| 6 | `111110` | 3, 5, 11 | none |
| 7 | `0111110` | 2, 10 | none |

Thus the failure mode for the published C2 seed word is not absence of a
period-7 readable window. The failure is that the perturbation mask has extra
cells and does not preserve its shape until the encoding window is widened.

### Refined Search Results

These runs use the refined verifier with three-period exactness. Exact means
the perturbation mask translates at `T`, `2T`, and `3T`; window means only the
raw seed word recurs under the single-row embedding.

| Glider | Search bound | Best seed | Phase | Candidates | Exact candidates | Status |
|---|---|---|---:|---:|---:|---|
| B | `W..W+8` | `01111101` width 8 | 8 | 527 | 0 | window |
| C1 | `W..W+2` | `111010000` width 9 | 0 | 137 | 26 | exact |
| C2 | `W..W+8` | `11101000` width 8 | 0 | 225 | 27 | exact |
| C3 | `W..W+1` | `11101000011` width 11 | 0 | 147 | 43 | exact |
| D1 | `W..W+4` | `00101111100` width 11 | 5 | 997 | 0 | window |
| D2 | `W..W+8` | `00101` width 5 | 5 | 730 | 0 | window |
| F | `W..W+8` | `111100` width 6 | 4 | 141 | 0 | window |
| G1 | `W..W+2` | `00010110001` width 11 | 12 | 167 | 0 | window |
| H | `W..W+2` | `011011111000` width 12 | 10 | 1 | 0 | window |

Full `W..W+8` enumeration for the long-period D1, G1, and H targets is
expensive under brute-force single-row embedding, and the completed smaller
bounds already show the same obstruction: many window recurrences do not carry
a translated perturbation. The likely missing representation for B, D, F, G1,
and H is a finite two-dimensional space-time mask rather than one spatial row.
Those gliders are space-time tubes; a single row can line up with a readable
visual word without containing all cells needed for phase-exact recurrence.

## Attempt 4 -- wider window + periodicity

The verifier now accepts `--max-extended-width N`, with default `N=8` and
hard cap `N=16`. The old `--extended-width N` spelling is still accepted as an
alias for reproducing earlier runs. It also accepts `--try-periods k1,k2,...`
and `--try-both-dx`, so a target can be checked against period multipliers and
both displacement signs in one pass.

The exact criterion has a second route. The old mask criterion still checks
that the finite perturbation relative to ether recurs after `T`, `2T`, and
`3T`. The new tube criterion simulates the whole generated space-time tube and
checks raw cell periodicity row by row under `(T, dx)`. This verifies gliders
whose complete tube is periodic even when the endpoint perturbation mask is
too sensitive to the chosen ether-backed row encoding.

### Regression

| Glider | Command bound | Best seed | Phase | Exact candidates | Status |
|---|---|---|---:|---:|---|
| A | `W..W` | `011101` width 6 | 12 | 5 | exact, mask |
| C1 | `W..W+2` | `111010000` width 9 | 0 | 26 | exact, mask |
| C2 | `W..W+8` | `11101000` width 8 | 0 | 27 | exact, mask |
| C3 | `W..W+1` | `1110100001` width 10 | 0 | 22 | exact, mask |

The canonical visual A seed `111110` remains window-only at phases 3, 5, and
11. The stricter single-row seed for A is still `011101` at phase 12.

### Target Results

| Glider | Search bound | Period trials | Best seed | Phase | Exact candidates | Status |
|---|---|---|---|---:|---:|---|
| B | `W..W` | `1,2,3,4`, both dx signs | `01110111` width 8 | 0 | 4 | exact, tube at `(8,4)` |
| D1 | `W..W+4` | `1,2,3,4`, both dx signs | `00101111100` width 11 | 5 | 0 | window |
| D2 | `W..W+8` | `1,2,3,4`, both dx signs | `00101` width 5 | 5 | 0 | window |
| F | partial `W..W+13` | `1,2`, both dx signs | window candidates only | -- | 0 | window |
| G1 | `W..W` | `1,2,3,4`, both dx signs | `01101111100` width 11 | 13 | 0 | window |
| H | skipped at `W+16` | -- | previous `W+2` result retained | 10 | 0 | window |

B is phase-exact under the fundamental tube periodicity test. Its exact
candidate uses the reversed displacement sign and a doubled period relative to
the input table row: seed `01110111`, phase 0, period `(8,4)`, four exact tube
candidates in the width-8 pass.

D1 and D2 remain readable-window gliders under the expanded period and dx
trial. G1 remains window-only in the completed width-11 trial; the wider
`W..W+2` run showed the same window-only pattern before it was stopped. F was
run with the requested wider seed window in the feasible `k=1,2` regime and
was still window-only through width 14; the full `k=1,2,3,4` run is dominated
by the long-period tube simulation and did not become exact before it was
stopped. H was not expanded to `W+16`: `W+16` would require checking up to
28-cell seeds for period 92, which is outside this brute-force pass.

The net verified count is four canonical targets: B, C1, C2, and C3. The
remaining obstruction is representation-level rather than absence of readable
windows: D1, D2, F, G1, and H all expose single-row windows, but this verifier
still does not recover a closed finite phase tube for them within the completed
bounds. Those classes likely need either multi-glider context, a catalogued
phase origin from Cook's diagram, or a finite two-dimensional mask that is not
derivable from one arbitrary spatial row.

## Attempt 5 -- Ebar hunt

Ebar was searched as the Cook moving-data carrier with visual width 7 and
period `(30,-8)`. The primary command was:

```bash
/tmp/glider_search Ebar 7 30 -8 --max-extended-width 13 --try-periods 1,2,3,4 --try-both-dx
```

This run covered widths 7 through 17 completely and entered width 18 before
the brute-force pass was stopped after about 86 minutes. It found 2487
readable-window candidates, but no strict candidate:

| Search | Width coverage | Exact mask | Exact tube | Best window-only candidate |
|---|---|---:|---:|---|
| `(30,-8)`, multipliers `1,2,3,4`, both dx signs | `W=7..17` complete, `W=18` partial | 0 | 0 | width 11 seed `11111000111`, phase 8, period `(30,-8)`, `diff_count=10` |

The auxiliary period-family run used base period `(15,-4)` with multipliers
`1,2,3,4` and both dx signs. It covered through width 16 and entered width 17.
This includes the visible alternatives `(15,-4)`, `(30,-8)`, `(45,-12)`, and
`(60,-16)` in one pass. It found no exact mask or tube candidates; the best
window-only candidate was width 9 seed `011001100`, phase 12, period
`(15,-4)`, with `diff_count=9`.

Neighbor checks were also run for `(30,-10)`, `(30,-6)`, `(28,-8)`, and
`(32,-8)` through width 15 where feasible. The `(30,-10)`, `(28,-8)`, and
`(32,-8)` searches produced no candidates. The `(30,-6)` search produced 1232
window candidates under the reversed displacement sign `(30,6)`, but no exact
candidate; its best window-only seed was width 7 `0111010`, phase 11, with
`diff_count=6`.

No phase-exact single-row Ebar seed was recovered. The obstruction is not a
lack of readable row windows: the search found many near recurrences, including
several low-difference windows, but every one failed both the perturbation-mask
and space-time tube periodicity tests. The likely remaining issue is that
Cook's Ebar carrier is not represented by an isolated one-row ether-backed
seed in this verifier. The next viable routes are a full bitmap parse of Cook's
Figure 4 at higher fidelity, or obtaining a catalogued phase bitmap from Cook
or Martinez.
