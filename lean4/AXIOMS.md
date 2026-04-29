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

| name | tier | signature | role | source_file | replaces_when |
|---|---|---|---|---|---|
| BEDC.FKernel.Mark.BMark         | carrier   | `Type`                                       | raw mark type                                                       | FKernel/Mark.lean       | (permanent) |
| BEDC.FKernel.Mark.b0            | primitive | `BMark`                                      | distinguished b0 mark constant                                       | FKernel/Mark.lean       | (permanent) |
| BEDC.FKernel.Mark.b1            | primitive | `BMark`                                      | distinguished b1 mark constant                                       | FKernel/Mark.lean       | (permanent) |
| BEDC.FKernel.Mark.msame         | primitive | `BMark → BMark → Prop`                       | mark sameness predicate                                              | FKernel/Mark.lean       | (permanent) |
| BEDC.FKernel.Hist.BHist         | carrier   | `Type`                                       | emission history type                                                | FKernel/Hist.lean       | (permanent) |
| BEDC.FKernel.Hist.Empty         | primitive | `BHist`                                      | empty emission history constant                                      | FKernel/Hist.lean       | (permanent) |
| BEDC.FKernel.Hist.e0            | primitive | `BHist → BHist`                              | E0 emission step                                                     | FKernel/Hist.lean       | (permanent) |
| BEDC.FKernel.Hist.e1            | primitive | `BHist → BHist`                              | E1 emission step                                                     | FKernel/Hist.lean       | (permanent) |
| BEDC.FKernel.Hist.hsame         | primitive | `BHist → BHist → Prop`                       | history sameness predicate                                           | FKernel/Hist.lean       | (permanent) |
| BEDC.FKernel.Ext.Ext            | primitive | `BHist → BMark → BHist → Prop`               | relational extension                                                 | FKernel/Ext.lean        | (permanent) |
| BEDC.FKernel.Cont.Cont          | primitive | `BHist → BHist → BHist → Prop`               | relational continuation                                              | FKernel/Cont.lean       | (permanent) |
| BEDC.FKernel.Ask.ProbeName      | carrier   | `Type`                                       | probe name type                                                      | FKernel/Ask.lean        | (permanent) |
| BEDC.FKernel.Ask.Evidence       | carrier   | `Type`                                       | evidence ledger type                                                 | FKernel/Ask.lean        | (permanent) |
| BEDC.FKernel.Ask.Ask            | primitive | `ProbeName → BHist → BMark → Evidence → Prop`| asking event predicate                                                | FKernel/Ask.lean        | (permanent) |
| BEDC.FKernel.Bundle.ProbeBundle | carrier   | `Type`                                       | probe bundle type                                                    | FKernel/Bundle.lean     | (permanent) |
| BEDC.FKernel.Bundle.Bnil        | primitive | `ProbeBundle`                                | empty probe bundle                                                   | FKernel/Bundle.lean     | (permanent) |
| BEDC.FKernel.Bundle.Bcons       | primitive | `ProbeName → ProbeBundle → ProbeBundle`      | probe bundle cons                                                    | FKernel/Bundle.lean     | (permanent) |
| BEDC.FKernel.Bundle.InBundle    | primitive | `ProbeName → ProbeBundle → Prop`             | probe-name in bundle predicate                                       | FKernel/Bundle.lean     | (permanent) |
| BEDC.FKernel.Sig.SigRel         | primitive | `ProbeBundle → BHist → BHist → Prop`         | signature generation relation                                        | FKernel/Sig.lean        | (permanent) |
| BEDC.FKernel.Package.Pi         | carrier   | `Type`                                       | bundle index type                                                    | FKernel/Package.lean    | (permanent) |
| BEDC.FKernel.Package.Pkg        | carrier   | `Type`                                       | package token type                                                   | FKernel/Package.lean    | (permanent) |
| BEDC.FKernel.Package.TokIntro   | primitive | `Pi → BHist → Pkg → Prop`                    | token introduction predicate                                         | FKernel/Package.lean    | (permanent) |
| BEDC.FKernel.Package.psame      | primitive | `Pkg → Pkg → Prop`                           | package sameness predicate                                           | FKernel/Package.lean    | (permanent) |
| BEDC.FKernel.Gap.Domain         | carrier   | `Type`                                       | source domain type                                                   | FKernel/Gap.lean        | (permanent) |
| BEDC.FKernel.Gap.InDom          | primitive | `Domain → BHist → Prop`                      | history-in-domain predicate                                          | FKernel/Gap.lean        | (permanent) |
| BEDC.FKernel.Gap.InGapSig       | primitive | `Pi → Domain → Pkg → BHist → Prop`           | signature gap membership predicate                                   | FKernel/Gap.lean        | (permanent) |
| BEDC.FKernel.NameCert.DerivedName     | carrier | `Type` | derived interface name type             | FKernel/NameCert.lean   | (permanent) |
| BEDC.FKernel.NameCert.SourceSpec      | carrier | `Type` | source specification type                | FKernel/NameCert.lean   | (permanent) |
| BEDC.FKernel.NameCert.PatternSpec     | carrier | `Type` | pattern specification type               | FKernel/NameCert.lean   | (permanent) |
| BEDC.FKernel.NameCert.ClassifierSpec  | carrier | `Type` | classifier specification type            | FKernel/NameCert.lean   | (permanent) |
| BEDC.FKernel.NameCert.StabilityCert   | carrier | `Type` | stability certificate type               | FKernel/NameCert.lean   | (permanent) |
| BEDC.FKernel.NameCert.LedgerPolicy    | carrier | `Type` | ledger policy type                       | FKernel/NameCert.lean   | (permanent) |
| BEDC.FKernel.Examples.Unary.UnaryHistory | provisional | `BHist → Prop`     | unary-history predicate placeholder            | FKernel/Examples/Unary.lean | concrete `Unary` instance lands as a `def` |
| BEDC.FKernel.Examples.Unary.UnaryBundle  | provisional | `ProbeBundle`      | unary-bundle constant placeholder              | FKernel/Examples/Unary.lean | concrete `Unary` instance lands as a `def` |
| BEDC.FKernel.Examples.Unary.UnaryDomain  | provisional | `Domain`           | unary-domain constant placeholder              | FKernel/Examples/Unary.lean | concrete `Unary` instance lands as a `def` |
| BEDC.FKernel.Examples.Unary.UnaryName    | provisional | `DerivedName`      | unary derived-name constant placeholder        | FKernel/Examples/Unary.lean | concrete `Unary` instance lands as a `def` |
| BEDC.BaseReflection.Hist        | carrier   | `Type`                                       | abstract carrier (paper-side scaffolding; independent from FKernel)  | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.SigObj      | carrier   | `Type`                                       | abstract signature object carrier                                    | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.Pkg         | carrier   | `Type`                                       | abstract package carrier                                             | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.Pi          | carrier   | `Type`                                       | abstract bundle index carrier                                        | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.Domain      | carrier   | `Type`                                       | abstract domain carrier                                              | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.Evidence    | carrier   | `Type`                                       | abstract evidence carrier                                            | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.hsame       | primitive | `SigObj → SigObj → Prop`                     | abstract signature sameness predicate                                | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.InDom       | primitive | `Domain → Hist → Prop`                       | abstract history-in-domain predicate                                 | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.SigGen      | primitive | `Pi → Hist → SigObj → Evidence → Prop`       | abstract signature generation predicate                              | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.TokIntro    | primitive | `Pi → SigObj → Pkg → Prop`                   | abstract token introduction predicate                                | BaseReflection.lean     | (permanent) |
| BEDC.BaseReflection.InGapSig    | primitive | `Pi → Domain → Pkg → Hist → Prop`            | abstract signature gap membership predicate                          | BaseReflection.lean     | (permanent) |

## Tier counts (current)

| tier | count |
|---|---|
| carrier     | 19 |
| primitive   | 24 |
| provisional |  4 |
| **total**   | **47** |

## Change history (high level)

The registry is amended in place; do not record version-by-version churn here.
The append-only history is in `git log`. When an axiom is retired (e.g.,
provisional → real `def`), remove its row in the same commit that lands
the new definition.
