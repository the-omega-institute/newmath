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
