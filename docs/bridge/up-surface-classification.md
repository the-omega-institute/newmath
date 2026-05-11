# BEDC Up Surface Classification

This note records a lightweight receiving index for the `BEDC.Derived.*Up`
surface. It is intentionally descriptive: it does not accept external content,
promote bridge packets, or authorize paper and Lean writes. It gives the bridge
runner and future agents a stable vocabulary for deciding which `*Up` material
is evidence, which material is a public surface, and which material still needs
operator review.

## Current Shape

The current `newmath` audit branch contains a large `*Up` surface under
`lean4/BEDC/Derived`:

- `1390` Lean files whose path or module name is part of an `*Up` surface.
- `264` distinct `*Up` module families.
- `992` `BEDC.lean` imports of `*Up` modules or submodules.
- No `sorry`, `admit`, or raw `axiom` matches were found in the scanned
  `*Up` files during this bridge review.

The largest module families by file count are:

| Family | Files |
| --- | ---: |
| `FieldUp` | 113 |
| `CategoryUp` | 82 |
| `SheafUp` | 80 |
| `OptionUp` | 70 |
| `TopGroupUp` | 55 |
| `RealUp` | 42 |
| `DiffFormUp` | 40 |
| `GroupUp` | 37 |
| `ListUp` | 36 |
| `ContinuousUp` | 31 |
| `PrimeUp` | 28 |
| `CurvatureUp` | 27 |

## Bridge Categories

The bridge should classify `*Up` material by role before it creates any durable
receiving artifact.

| Category | Meaning | Default Bridge Status |
| --- | --- | --- |
| Source and classifier surfaces | Files named around `Source`, `SourceSpec`, `Carrier`, or `Classifier`; these define the input face or recognition layer for a BEDC instance. | observed |
| Name certificate surfaces | Files named around `NameCert`, `NameCertificate`, `Namecert`, or using `SemanticNameCert`; these are public certificate interfaces and are the strongest candidates for receiving indexes. | candidate |
| Public/export surfaces | Files named around `Public`, `Export`, or `Surface`; these are the safest NewMath-side targets for lightweight Automath evidence summaries. | candidate |
| Obligation and boundary surfaces | Files named around `Obligation`, `Boundary`, `Scope`, or `Seed`; these record what must not be promoted without review. | needs_operator_review |
| Consumer and downstream surfaces | Files named around `Consumer` or `Downstream`; these describe how another layer may consume an instance. | needs_operator_review |
| Ledger and readback surfaces | Files named around `Ledger` or `Readback`; these are useful for audit trails and traceable bridge decisions. | candidate |
| Exactness surfaces | Files named around `Exactness`, `Determinacy`, `Uniqueness`, `Exhaustion`, or `Coverage`; these are the preferred targets when Automath evidence is mathematical rather than operational. | candidate |
| TasteGate witnesses | Files named `TasteGate` or containing a `taste_gate` witness; these are mandatory boundaries for AI-origin BEDC content leaving seed status. | protected |

## Current Hit Counts

The scan used filename and content markers, so categories can overlap.

| Marker Group | File Hits |
| --- | ---: |
| Name certificate | 433 |
| Source or classifier | 154 |
| Obligation or boundary | 119 |
| Public or export surface | 88 |
| Exactness or determinacy | 75 |
| Consumer or downstream | 50 |
| Semantic certificate | 50 |
| Standard bridge | 49 |
| Ledger | 48 |
| Readback | 39 |
| TasteGate | 3 |

## Bridge Policy

Automath-to-NewMath evidence should first target public, exactness, ledger, or
name-certificate surfaces. Those targets can receive lightweight review indexes
without creating BEDC paper or Lean content directly.

NewMath-to-Automath material should not be copied into Automath paper or Lean
from this classification alone. Automath receiving content must pass the native
Killo/golden writeback lane. If a NewMath `*Up` record is still marked
`blocked_automath_not_ready`, the correct output is a review packet or manifest
note, not a durable Automath theorem or paragraph.

AI-origin BEDC seed material remains protected until the relevant `TasteGate`
witness and operator decision are recorded.
