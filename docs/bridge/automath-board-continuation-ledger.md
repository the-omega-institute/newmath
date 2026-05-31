# Automath BOARD Continuation Ledger

This durable ledger records Automath-to-NewMath bridge candidates that were shaped as evidence-backed BEDC continuation targets.
Runtime inbox, state, logs, and raw gate output remain untracked.

## Candidate Modes

Read the bridge contract in `docs/bridge/automath-newmath-bridge.md`.
Read current bridge runtime outputs from:

- `tools/automath_newmath_bridge/out/`
- `tools/automath_newmath_bridge/state/`
- `tools/automath_newmath_bridge/logs/`

Use `tools/automath_newmath_bridge/render_bridge_report.py` to render the
current report from runtime data.

## Policy

- `evidence_only` records are reference material; they should not create BEDC theorem work automatically.
- `board_continuation` records enter BOARD only as continuation targets with Automath evidence packets.
- `proposal_seed_candidate` records may seed a BEDC-native proposal, but still go through native intake gates.
- BEDC workers should inspect the Automath evidence first and write only the minimal BEDC-native wrapper, proposal, audit task, or rejection reason.
- Machine-readable ACK/NACK status may be written to an ignored local bridge
  runtime ledger; it is not committed to the BEDC branch.
