# Cook collision design notes

This note prepares the Phase B collision table for the Rule 110 Cook encoder.
It is a design document, not an implementation contract: entries marked
`TBD via direct Rule 110 simulation` must not be treated as verified lookup
rows until a local simulator reproduces the claimed before/after spacetime
diagram.

## Sources and trust posture

Primary source:

- Matthew Cook, "Universality in Elementary Cellular Automata", Complex
  Systems 15(1):1-40, 2004:
  <https://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf>. The relevant
  parts are section 3 for the ether and particle catalog, section 4 for
  interactions, and sections 5-6 for the cyclic tag system construction.

Secondary sources:

- Genaro J. Martinez, Harold V. McIntosh, Juan C. Seck-Tuoh-Mora, and Sergio V.
  Chapa-Vergara, "Reproducing the cyclic tag system developed by Matthew Cook
  with Rule 110 using the phases fi_1": <https://arxiv.org/abs/1307.7951>. This
  is useful for phase-sensitive encodings and for reading Cook's symbolic
  particle notation.
- Stephen Wolfram, A New Kind of Science, page 689 and page 1116 notes:
  <https://www.wolframscience.com/nks/p689--the-rule-110-cellular-automaton/>
  and
  <https://www.wolframscience.com/nks/notes-11-8--initial-conditions-for-rule-110/>.
  These are useful for scale estimates and contextual claims about Cook's cyclic
  tag system construction.
- Wikipedia, "Rule 110": <https://en.wikipedia.org/wiki/Rule_110>, for a compact
  public summary of universality, ether, gliders, and cyclic-tag-system
  simulation. It is not authoritative for exact collision products.
- McIntosh and Martinez online Rule 110 atlas pages:
  <https://delta.cs.cinvestav.mx/~mcintosh/comun/RULE110W/RULE110.html> and
  <https://delta.cs.cinvestav.mx/~mcintosh/comun/summer2001/bookcollisionsHtml/bookcollisions.html>,
  for secondary phase and collision indexes.

The implementation must prefer local Rule 110 simulation evidence over any
secondary summary.

## Glider zoo recap

Cook describes Rule 110 as an ether background interrupted by localized
particles. The named particle families are conventionally written `A` through
`H`, plus a periodic glider gun. Cook's catalog uses spacetime displacement
relative to the ether, so a velocity is a slope in cells per generation. The
table below records the working design values used for planning. Exact phase
placement remains a separate implementation issue.

| ID | Role in design notes | Working velocity | Period / displacement | Implementation note |
| --- | --- | --- | --- | --- |
| `A` | Small positive-slope particle, simplest catalog entry | `2/3` | displacement 2 cells over 3 generations | Current C implementation uses a best-effort visible pattern over ether, not a phase-complete Cook table. |
| `B` | Small negative-slope particle family used in several interactions | `-2/4 = -1/2` | displacement -2 over 4 generations | Includes related barred and hatted `B` families with the same nominal speed. |
| `C` | Stationary support family with alignments `C1`, `C2`, `C3` | `0/7 = 0` | zero displacement over 7 generations | Subscripts identify ether alignments, not different slopes. |
| `D` | Positive-slope particle family participating in productive interactions | `2/10 = 0.2` | displacement 2 over 10 generations | `D1` and `D2` share the speed but differ by alignment and footprint. |
| `E` | Composite negative-slope family | `-4/15` for `E_n`; `-8/30` for barred `E` | same nominal speed, different footprint | The visible footprint is wide enough that naive row-0 snippets are unsafe. |
| `F` | Composite negative-slope family | `-4/36 = -1/9` | displacement -4 over 36 generations | Requires multi-row phase extraction. |
| `G` | Rare or wide negative-slope family | `-14/42 = -1/3` | displacement -14 over 42 generations | Do not implement from memory; extract from Cook figure or simulation catalog. |
| `H` | Rare or wide negative-slope family | `-18/92` | displacement -18 over 92 generations | Do not implement from memory; extract from Cook figure or simulation catalog. |
| gun | Periodic source producing a stream of smaller particles | `-20/77` for the whole source footprint | emits `A` and `B` gliders once per cycle in Cook's catalog | Must be represented as a phase-aligned multi-particle structure, not as a single glider. |

The velocity entries above follow the secondary tabulation in Martinez et al.
and must still be checked against Cook's diagrams for phase-exact templates.
Cook's figure 4 also distinguishes variants such as `A2`, `A3`, `A4`,
barred/hatted `B`, and `C1` through `D2`. For the C catalog, each glider should
eventually have:

- a symbolic ID,
- a list of phase bitmasks,
- width per phase,
- horizontal displacement after one full period,
- period in generations,
- far-field ether alignment before and after each phase.

## Collision matrix

The full `A`-through-`H` pair matrix is not directly recoverable from the
accessible text alone. Cook section 4 presents specific interactions useful for
the cyclic tag construction rather than an exhaustive ordered table. The table
therefore separates known construction motifs from unknown generic pair rows.

Legend:

- `annihilation`: no localized particle remains after the collision tail clears.
- `stable package`: output is a recognizable particle or particle bundle after
  transient debris is gone.
- `productive`: collision creates a particle or packet used by the cyclic tag
  system machinery.
- `TBD via direct Rule 110 simulation`: no trusted outcome should be hard-coded
  yet.

| Incoming 1 | Incoming 2 | Expected outcome | Status |
| --- | --- | --- | --- |
| `A` | `A` | phase-dependent; may pass, bind, or annihilate depending on spacing | TBD via direct Rule 110 simulation |
| `A` | `B` | phase-dependent stable package or annihilation | TBD via direct Rule 110 simulation |
| `A` | `C` | possible productive interaction in Cook diagrams | TBD via direct Rule 110 simulation |
| `A` | `D` | possible productive interaction in Cook diagrams | TBD via direct Rule 110 simulation |
| `A` | `E` | phase-dependent interaction, likely wide transient | TBD via direct Rule 110 simulation |
| `A` | `F` | phase-dependent interaction, likely wide transient | TBD via direct Rule 110 simulation |
| `A` | `G` | unknown | TBD via direct Rule 110 simulation |
| `A` | `H` | unknown | TBD via direct Rule 110 simulation |
| `B` | `B` | unknown | TBD via direct Rule 110 simulation |
| `B` | `C` | construction-relevant in ossifier/data interactions when phase-aligned | TBD via direct Rule 110 simulation |
| `B` | `D` | construction-relevant in ossifier/data interactions when phase-aligned | TBD via direct Rule 110 simulation |
| `B` | `E` | unknown | TBD via direct Rule 110 simulation |
| `B` | `F` | unknown | TBD via direct Rule 110 simulation |
| `B` | `G` | unknown | TBD via direct Rule 110 simulation |
| `B` | `H` | unknown | TBD via direct Rule 110 simulation |
| `C` | `C` | unknown | TBD via direct Rule 110 simulation |
| `C` | `D` | construction-relevant candidate; likely produces a stable outgoing packet in selected phases | TBD via direct Rule 110 simulation |
| `C` | `E` | unknown | TBD via direct Rule 110 simulation |
| `C` | `F` | unknown | TBD via direct Rule 110 simulation |
| `C` | `G` | unknown | TBD via direct Rule 110 simulation |
| `C` | `H` | unknown | TBD via direct Rule 110 simulation |
| `D` | `D` | unknown | TBD via direct Rule 110 simulation |
| `D` | `E` | construction-relevant candidate in leader/ossifier cleanup | TBD via direct Rule 110 simulation |
| `D` | `F` | unknown | TBD via direct Rule 110 simulation |
| `D` | `G` | unknown | TBD via direct Rule 110 simulation |
| `D` | `H` | unknown | TBD via direct Rule 110 simulation |
| `E` | `E` | unknown | TBD via direct Rule 110 simulation |
| `E` | `F` | construction-relevant candidate in wide packet interactions | TBD via direct Rule 110 simulation |
| `E` | `G` | unknown | TBD via direct Rule 110 simulation |
| `E` | `H` | unknown | TBD via direct Rule 110 simulation |
| `F` | `F` | unknown | TBD via direct Rule 110 simulation |
| `F` | `G` | unknown | TBD via direct Rule 110 simulation |
| `F` | `H` | unknown | TBD via direct Rule 110 simulation |
| `G` | `G` | unknown | TBD via direct Rule 110 simulation |
| `G` | `H` | unknown | TBD via direct Rule 110 simulation |
| `H` | `H` | unknown | TBD via direct Rule 110 simulation |
| gun | `A` stream | emits a periodic packet stream | Known qualitatively from Cook; exact phase and spacing TBD |
| leader package | ossifier package | advances active production marker and prepares a data interaction | Known qualitatively from Cook sections 5-6; exact low-level particles TBD |
| data bit `0` package | active ossifier | deletes consumed symbol and emits no production payload | Known construction behavior; particle-level table TBD |
| data bit `1` package | active ossifier | deletes consumed symbol and emits the current production payload | Known construction behavior; particle-level table TBD |

The lookup function planned in B1 should therefore start with a typed outcome
that can represent uncertainty:

- `COOK_COLLISION_UNKNOWN`
- `COOK_COLLISION_ANNIHILATION`
- `COOK_COLLISION_PRODUCTS`
- `COOK_COLLISION_PHASE_DEPENDENT`

The future B2 test suite can tighten `UNKNOWN` rows one by one. It should not
pretend that a single unordered pair is enough when phase and separation change
the product.

## Productive construction interactions

Cook's universality construction does not require an arbitrary particle collider.
It requires a controlled periodic computation built from three high-level
families:

- a leader, which marks the start of the active computation cycle,
- ossifiers, one per cyclic-tag-system production,
- a data block, which represents the current tape symbols.

The productive collisions are the interactions between those families:

| Construction interaction | Logical effect | Collision-table dependency |
| --- | --- | --- |
| leader meets first ossifier | establishes the active production cycle | Need exact leader and ossifier particle packages. |
| leader/clock packet passes an inactive ossifier | advances to the next production without corrupting the data block | Need pass-through or regeneration collisions. |
| active ossifier meets data `0` symbol | consumes the leading `0` and appends nothing | Need annihilation or cleanup collision plus continued clock packet. |
| active ossifier meets data `1` symbol | consumes the leading `1` and appends the production word | Need one collision family per emitted bit pattern. |
| production payload meets tail of data block | appends emitted symbols at the correct spacing | Need stable join collisions and tail cleanup. |
| cycle-completion packet meets leader region | resets phase for the next production index | Need phase-restoring collision. |

Cook sections 5 and 6 describe these as a cyclic-tag-system emulator rather than
as independent physics experiments. The implementation should preserve that
hierarchy: construct leader, ossifier, and data block packages first, then derive
their actual low-level particle pair rows by simulation.

## Direct simulation verification strategy

Every collision row must be verified against the local Rule 110 evaluator before
it becomes part of a trusted lookup table.

### Initial substrate

Use the known ether word as the far-field background. For each test:

1. Allocate a wide one-dimensional row, with guard ether on both sides.
2. Emit ether for at least several periods beyond both expected light cones.
3. Inject glider 1 in a known phase at position `p1`.
4. Inject glider 2 in a known phase at position `p2`.
5. Choose `p2 - p1` so the particles collide inside the guard region after a
   predictable number of generations.

The test fixture should store phase IDs and initial separation explicitly. A
collision row without phase IDs is incomplete.

### Evolution window

Run the evaluator for three intervals:

- pre-collision: enough steps to confirm each injected particle moves as the
  isolated catalog predicts,
- interaction: enough steps for their light cones to overlap,
- cooling: enough steps after the collision for transient debris to separate or
  vanish.

The cooling interval is essential. Rule 110 collisions can create short-lived
localized disturbances that are not final products.

### Observation

Observation should be algorithmic, not manual screenshot inspection:

1. Compare the evolved row against ether to extract non-ether islands.
2. Track each island over time and estimate slope.
3. Match each stable island against the known phase catalog.
4. Treat unmatched persistent islands as `UNKNOWN_PRODUCT`, not as failure by
   default.
5. Treat a clean return to ether as `annihilation`.

For early Phase B, a manual visual dump is acceptable as a debugging aid, but
the committed test should use deterministic row comparisons.

### Acceptance rule for a collision entry

A collision lookup row becomes checked only when:

- the isolated incoming glider phases pass their own catalog tests,
- the same initial condition reproduces on repeated runs,
- guard ether remains intact outside the causal cone,
- every outgoing stable island is classified,
- the observed displacement after one or more periods matches the product
  glider's catalog velocity.

## Data model implications

The collision table should not be keyed only by `(GliderId, GliderId)`. A useful
Phase B data model needs:

- incoming glider IDs,
- incoming phase IDs,
- relative separation in cells,
- orientation or ordering,
- expected transient duration,
- outgoing product list with phase IDs and offsets,
- confidence state: `from_primary_diagram`, `from_secondary_source`,
  `simulated_checked`, or `unknown`.

This keeps the table honest while Phase A's glider catalog is still incomplete.

## Open questions

- Exact `B` through `H` velocities and period/displacement pairs must be read
  from Cook's catalog diagrams or a trusted phase table before implementation.
- The glider gun should be represented as a periodic source package; its emitted
  particle sequence and period need direct extraction.
- Cook's section 4 diagrams show selected interactions, but the accessible text
  does not provide a complete machine-readable all-pairs matrix.
- Construction-critical leader, ossifier, and data block packages may be better
  implemented as higher-level bit-pattern templates before decomposing them into
  named `A`-through-`H` particles.
- Some outcomes are inherently phase-dependent, so the future API should expose
  phase and separation rather than hiding uncertainty behind a single pair row.
