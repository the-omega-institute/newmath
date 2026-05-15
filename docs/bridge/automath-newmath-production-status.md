# Automath-NewMath Production Status

This durable status explains why the bridge did or did not produce new BEDC BOARD continuation output.
Runtime inbox, state, raw gate output, and logs remain untracked.

| Metric | Value |
| --- | --- |
| Production reason | `all_specific_board_candidates_duplicate_or_history_rejected` |
| Apply BOARD ingest | `True` |
| Eligible BOARD candidates this pass | `0` |
| Duplicate/history-skipped titles | `3` |
| Accepted into BOARD | `0` |
| Rejected by BOARD | `0` |
| ACK rows emitted this pass | `9` |

## Status Counts

| Status | Count |
| --- | ---: |
| `blocked` | 3 |
| `consumed` | 3 |
| `evidence_only` | 3 |

## Reason Counts

| Reason | Count |
| --- | ---: |
| `duplicate_board_title` | 3 |
| `evidence_only:pipeline_status` | 3 |
| `no_specific_board_claim` | 3 |

## Source Commits

| Commit | Rows |
| --- | ---: |
| `f76f46f07a1a48d5c12a20c2f8d366bb9df9330d` | 9 |

## Production Discipline

- BOARD entries must be evidence-backed continuation targets, not vague requests to research Automath again.
- `evidence_only` rows are acknowledged for Automath feedback but do not spawn BEDC theorem work.
- `blocked` rows tell Automath why a candidate did not become a BEDC continuation target.
- New production requires either a new source commit, a sharper source-specific BEDC landing object, or a BEDC ACK that changes the retry priority.
