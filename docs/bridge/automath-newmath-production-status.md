# Automath-NewMath Production Status

This durable status explains why the bridge did or did not produce new BEDC BOARD continuation output.
Runtime inbox, state, raw gate output, and logs remain untracked.

| Metric | Value |
| --- | --- |
| Production reason | `candidate_output_available` |
| Apply BOARD ingest | `True` |
| Eligible BOARD candidates this pass | `3` |
| Duplicate/history-skipped titles | `3` |
| Accepted into BOARD | `0` |
| Rejected by BOARD | `3` |
| ACK rows emitted this pass | `9` |

## Status Counts

| Status | Count |
| --- | ---: |
| `blocked` | 4 |
| `consumed` | 2 |
| `evidence_only` | 3 |

## Reason Counts

| Reason | Count |
| --- | ---: |
| `duplicate_board_title` | 2 |
| `evidence_only:pipeline_status` | 3 |
| `history_rejected:too_vague` | 1 |
| `too_vague` | 3 |

## Source Commits

| Commit | Rows |
| --- | ---: |
| `aecb76a5a5eed83cc6bdbb981b51ebfb58dd695f` | 9 |

## Production Discipline

- BOARD entries must be evidence-backed continuation targets, not vague requests to research Automath again.
- `evidence_only` rows are acknowledged for Automath feedback but do not spawn BEDC theorem work.
- `blocked` rows tell Automath why a candidate did not become a BEDC continuation target.
- New production requires either a new source commit, a sharper source-specific BEDC landing object, or a BEDC ACK that changes the retry priority.
