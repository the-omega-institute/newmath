# BEDC Lean mirror

This `lean4/` tree is the Phase 1 mirror-port scaffold for BEDC.

- Toolchain: `leanprover/lean4:v4.28.0`
- Dependency policy: mathlib-free by design
- Verification and audit status are read from the local gates, not recorded here.

Use these commands from the repository root:

```sh
cd lean4
lake build
cd ..
python3 tools/check-axioms.py
python3 lean4/scripts/bedc_ci.py audit
python3 lean4/scripts/bedc_ci.py axiom-purity
```
