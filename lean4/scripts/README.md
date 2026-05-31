# BEDC formalization scripts

`codex_formalize.py` runs codex-driven Lean work in isolated git worktrees. The adapted pipeline keeps the automath architecture: Phase B target selection, gate, Phase C implementation, and Phase D verification/merge.

## Files
- `codex_formalize.py` — orchestrator for parallel formalization rounds on `lean4-codex-auto-dev`
- `lake_gate.py` — host-wide concurrency gate for `lake` (`LAKE_GATE_MAX_PARALLEL=2` by default)
- `bedc_ci.py` — BEDC audit/inventory/verification helpers
- `prompts/phase_b.txt` — target-selection prompt for BEDC
- `prompts/phase_c.txt` — implementation prompt for BEDC

## Typical commands
```bash
python3 lean4/scripts/codex_formalize.py --dry-run --status
python3 lean4/scripts/lake_gate.py env -- lean --version
python3 lean4/scripts/bedc_ci.py audit
python3 lean4/scripts/bedc_ci.py inventory --json
```

## BEDC invariants baked into the pipeline
- mathlib-free: prompts forbid `import Mathlib...` and direct the model to use Lean 4 stdlib only
- zero axiom: prompts forbid `axiom`, and `tools/check-axioms.py` remains the CI gate
- zero sorry: prompts require real proofs only; stuck targets must be dropped rather than left partial
- setup-driven design: prompts direct the model to reuse `[AskSetup]`, `[PackageSetup]`, `[DomainSetup]`, `[NameCertSetup]`, and `BaseReflectionSetup`

## Notes
- Worktrees live under `.worktrees/` and logs under `lean4/scripts/logs/`.
- `bedc_ci.py verify-files` runs `lake env lean` on explicit files; the orchestrator itself uses `lake_gate.py` for build concurrency.
- Run a real formalization round only after reviewing the adapted prompts and dry-run output.

## Script Help

`bedc_ci.py` is the source of truth for its current subcommands, options, and
machine-readable output:

```bash
python3 lean4/scripts/bedc_ci.py --help
python3 lean4/scripts/bedc_ci.py <subcommand> --help
python3 lean4/scripts/bedc_ci.py <subcommand> --json
```

## BEDC.MetaCIC.HostBridge — host Lean ↔ MetaCIC reflection

`lean4/BEDC/MetaCIC/HostBridge.lean` provides:

- `reflectExpr : Lean.Expr → MetaM (Option Term)` — best-effort
  translation from host Lean `Expr` to `BEDC.MetaCIC.Term`. Covers
  `sort`, `bvar`, `app`, `lam`, `forallE`, `const`, `fvar`, `mdata`.
- `#reflect_metacic <term>` elab command — print MetaCIC encoding of
  a host Lean term in the InfoView.

This module is the entry point for downstream BEDC automation that
wants to operate on the MetaCIC encoding of host theorems. The
metaprogramming layer is outside the pure-CIC discipline by design
(it consumes Lean elaboration data); the output `Term` values
remain pure-CIC data.
