# BEDC Axiom Registry

This file is the single source of truth for `axiom` declarations in `lean4/BEDC/`.

The audit script `tools/check-axioms.py` rejects any `axiom` declaration in
`lean4/BEDC/**/*.lean` whose fully qualified name does not appear here. Pull
requests that add, rename, or remove axioms must update this registry in the
same change.

The audit runs in CI (`.github/workflows/lake-build.yml`).

## Why a registry

`lean4/` is intentionally **mathlib-free**. BEDC is built bottom-up from
abstract carriers and primitive predicates; mathlib's pre-built mathematical
universe is deliberately not imported. Without the discipline of a closed
list, `axiom` becomes the path of least resistance for unprovable claims.
The registry forces every axiom to be written down in one place with a
declared role and a tier.

## Tiers

- **carrier** — abstract `Type`. A BEDC primitive carrier with no
  definitional content. Permanently axiomatic. Examples: `BMark`, `BHist`,
  `Pkg`, `Domain`. A new carrier axiom requires a corresponding entry in
  the paper-side claim registry and a written justification for why it is
  primitive (i.e., why it cannot be defined).

- **primitive** — predicate, relation, or constant directly on Tier 1
  carriers. Examples: `msame`, `hsame`, `b0`, `Empty`, `e0`, `Ext`, `Ask`.
  Permanently axiomatic; a primitive cannot be reduced to other axioms.

- **provisional** — temporary axiom that should eventually become a `def`
  or be eliminated. Each provisional row must record `replaces_when` —
  the condition under which the axiom is retired. Examples are `Examples/`
  scaffolding axioms that placeholder concrete instances.

## Adding an axiom

1. Add the `axiom` declaration in the appropriate `lean4/BEDC/.../<file>.lean`.
2. Add a row to the registry below (see schema). Tier and `replaces_when`
   must be set conservatively.
3. Run `python3 tools/check-axioms.py` locally to confirm parity.
4. Open the PR. CI will reject the PR if registry and source disagree.

## Schema

Columns:

- `name` — fully qualified Lean name (e.g., `BEDC.FKernel.Mark.BMark`)
- `tier` — `carrier` | `primitive` | `provisional`
- `signature` — the type signature as it appears in the `axiom` declaration
- `role` — one-line plain-language description
- `source_file` — relative path under `lean4/BEDC/`
- `replaces_when` — for provisional only; otherwise `(permanent)`

## Registry

**Current axiom count: 0.**

BEDC encodes its primitives as `inductive` types, `def` definitions, or
`class`/`structure` setup fields. There are no global `axiom` declarations
in `lean4/BEDC/`.

The registry table is therefore empty. If a future change introduces a global
`axiom`, add its row here in the same change and rerun
`python3 tools/check-axioms.py`.

## Tier counts (current)

| tier | count |
|---|---|
| carrier     | 0 |
| primitive   | 0 |
| provisional | 0 |
| **total**   | **0** |
