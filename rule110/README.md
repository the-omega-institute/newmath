# rule110 — BEDC ground-up minimal-trust kernel (vertical slice)

This is a sibling experiment to `lean4/BEDC/` and `papers/bedc/`. It ships a
5-7 day vertical slice demonstrating that the core finite-kernel theorems
from `lean4/BEDC/FKernel/Mark.lean` (the four `msame` lemmas) can be encoded
into a **cyclic tag system** and executed on a **~80-line ANSI C evaluator**,
with element trust ≪ Lean kernel.

## Trust chain

```
Layer 0: ANSI C compiler (universal, not audited)
Layer 1: Rule 110 evaluator     evaluator/rule110.c       (~50 LOC)
Layer 2: Cyclic tag evaluator   evaluator/cyclic_tag.c    (~80 LOC)
Layer 3: GroundCompiler encoder encoder/groundcompiler_encoding.c (~120 LOC)
Layer 4: Mark theorem manifests manifests/mark/*.ct        (8 files)
Layer 5: Self-consistent tests  tests/*.c                  (~500 LOC)

(Layer 6, Cook construction cyclic-tag→Rule-110 encoder, is milestone-2 scope,
not shipped in this slice. Rule 110 evaluator is shipped + verified via
binary counter toy demo, but its connection to Mark manifests is deferred.)
```

## Reproducibility

```bash
make            # builds all evaluators + tests
make test       # runs Layer A unit tests + Layer B round-trip + Layer C manifest assertions
make clean      # removes all build output
```

## Documentation

- `docs/trust_chain.md` — per-layer audit checklist
- `docs/manifest_format.md` — cyclic-tag manifest format spec
- `docs/theorem_encoding.md` — how 4 msame lemmas map to manifests

## Sources / convention

- Encoding: `lean4/BEDC/GroundCompiler/ChannelEncoding.lean` (escape-based variable-length, terminator `b1 b1`)
- Reject reason taxonomy: `lean4/BEDC/GroundCompiler/MinimalPrototype.lean`
- Theorems encoded: `lean4/BEDC/FKernel/Mark.lean` (`msame_refl`, `msame_symm`, `msame_trans`, `msame_no_confusion`)
- Cook 2004 reference: [Universality in Elementary Cellular Automata](http://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf)
- Full design rationale: `docs/superpowers/specs/2026-05-12-rule110-init-design.md`
- Implementation plan: `docs/superpowers/plans/2026-05-12-rule110-init.md`

## License

GPOL v1.0 — see `LICENSE`.
