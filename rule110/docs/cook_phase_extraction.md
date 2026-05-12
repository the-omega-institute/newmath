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
