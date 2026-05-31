# Automath-NewMath PI Reflection

This report is the deterministic PI layer for the Automath-to-NewMath bridge.
It turns global ACK/NACK and gate signals into disciplined bridge-control actions.
It does not write BEDC paper or Lean content.

## Runtime Sources

Read the bridge contract in `docs/bridge/automath-newmath-bridge.md`.
Read current ACK/NACK, gate, action, status, and reason data from:

- `tools/automath_newmath_bridge/out/`
- `tools/automath_newmath_bridge/state/`
- `tools/automath_newmath_bridge/logs/`

Use `tools/automath_newmath_bridge/render_bridge_report.py` to render the
current report from runtime data.

## Control Policy

- Repeated `no_specific_board_claim` creates refinement targets instead of resubmitting vague BOARD entries.
- `history_rejected:too_vague` cools unchanged retries until a narrower BEDC-native continuation claim exists.
- `duplicate_board_title` is treated as consumed unless the source commit or BEDC landing object changes.
- `evidence_only:pipeline_status` remains harness evidence and is not promoted to theorem work.
- The PI may write only durable bridge reports and action ledgers; runtime inbox, out, state, and logs remain uncommitted.
