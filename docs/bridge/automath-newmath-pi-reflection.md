# Automath-NewMath PI Reflection

This report is the deterministic PI layer for the Automath-to-NewMath bridge.
It turns global ACK/NACK and gate signals into disciplined bridge-control actions.
It does not write BEDC paper or Lean content.

## Current Signal

- ACK rows: `9`
- Gate rows: `15`
- PI actions: `5`
- Refinement targets: `3`

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
| `no_specific_board_claim` | 3 |

## PI Actions

| Action | Trigger | Effect | Severity |
| --- | --- | --- | --- |
| `pi:newmath:expand_specific_board_claims` | `no_specific_board_claim` | `refinement_queue_written` | `high` |
| `pi:newmath:narrow_history_rejected_too_vague` | `history_rejected:too_vague` | `cooldown_unchanged_retry` | `high` |
| `pi:newmath:cooldown_duplicate_board_titles` | `duplicate_board_title` | `do_not_resubmit_without_source_commit_or_title_change` | `medium` |
| `pi:newmath:keep_pipeline_status_evidence_only` | `evidence_only:pipeline_status` | `retain_as_evidence_only` | `low` |
| `pi:newmath:cycle_health` | `global_signal_summary` | `monitor_next_cycle` | `info` |

## Control Policy

- Repeated `no_specific_board_claim` creates refinement targets instead of resubmitting vague BOARD entries.
- `history_rejected:too_vague` cools unchanged retries until a narrower BEDC-native continuation claim exists.
- `duplicate_board_title` is treated as consumed unless the source commit or BEDC landing object changes.
- `evidence_only:pipeline_status` remains harness evidence and is not promoted to theorem work.
- The PI may write only durable bridge reports and action ledgers; runtime inbox, out, state, and logs remain uncommitted.
