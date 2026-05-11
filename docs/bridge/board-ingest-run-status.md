# Bridge BOARD Ingest Run Status

## Current Result

The Automath-to-NewMath bridge was run through the real BEDC BOARD adapter on
the local `bridge/newmath-automath-consumption` branch. This was not a harness
health check: the adapter called BEDC `board_spawn` with eligible bridge
candidates.

| Field | Value |
| --- | --- |
| Gate result count | `14` |
| Gate-passed count | `14` |
| BOARD-eligible candidates | `3` |
| `board_spawn` result | `ok` |
| Accepted into BOARD | `0` |
| Appended BOARD ids | none |
| Rejected count | `3` |

The three eligible candidates were Automath Lean theorem sources:

| Source | Intake result |
| --- | --- |
| `lean4/Omega/CircleDimension/KilloGodelCompressionNotFiniteRankHomologizable.lean` | rejected by BEDC BOARD gate |
| `lean4/Omega/CircleDimension/KilloGrothendieckCompletionPreservesInjection.lean` | rejected by BEDC BOARD gate |
| `lean4/Omega/CircleDimension/KilloS4BurnsideKaniRosenPrymSquare.lean` | rejected by BEDC BOARD gate |

The BEDC gate reported that all three candidates were deduplicated against
existing BOARD titles. Therefore these scanned Automath items are not waiting
for recognition in `tools/bedc-deep/BOARD.md`. They should remain review
evidence unless a later pass finds a more specific, non-duplicate BEDC target.

## Operational Fixes From This Run

The run exposed three production blockers and fixed them in the bridge branch:

- the NewMath bridge config now points at the actual local Automath worktree,
  `../automath`, rather than a non-existent `../automath-bridge`;
- bridge path resolution now checks paths relative to the config directory,
  the repo root, and the repo parent, so sibling worktrees resolve reliably;
- the scanner supports `--scan-limit-per-rule`, so production passes can avoid
  expensive full-repo content scans before candidate selection;
- BEDC file locks now use `msvcrt` on Windows and `fcntl` on POSIX, allowing
  local Windows BOARD-gate execution.

## Policy Consequence

A gate-passed bridge record is not the same as a BOARD item. BOARD ownership
remains with BEDC `board_spawn`: fit, novelty, deduplication, paper coverage,
and judge behavior decide whether a bridge candidate becomes a target. Current
Automath-to-NewMath outputs reached that gate and were rejected as duplicates.
