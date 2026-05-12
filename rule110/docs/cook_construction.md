# Cook construction status and design summary

This document summarizes the Rule 110 Cook-construction layer in `rule110/`.
It records the current encoder pipeline, the trust posture, and the test
surface. The repository has a deterministic Rule 110 substrate scaffold with
ether, named glider emitters, leader, ossifier, data block, collision
observation, and an empty cyclic-tag encoder path. It does not yet contain a
phase-exact Cook 2004 cyclic-tag-system construction.

## 1. Cook 2004 overview

Matthew Cook's universality proof shows that Rule 110 can simulate cyclic tag
systems. Rule 110 is the elementary cellular automaton with this local table:

```text
111 -> 0
110 -> 1
101 -> 1
100 -> 0
011 -> 1
010 -> 1
001 -> 1
000 -> 0
```

A cyclic tag system has a cyclic list of production words, a finite binary
tape, and a production pointer. At each step it deletes the first tape symbol.
If that symbol is `1`, it appends the current production word. If the symbol is
`0`, it appends nothing. The production pointer advances either way.

Cook's construction does not place those tape bits directly into a Rule 110
row. It builds a particle machine over the periodic Rule 110 ether. Localized
defects in the ether behave as gliders. Correctly phased packets of gliders
collide so that the cellular automaton realizes the cyclic tag step rule.

The construction uses several roles:

- ether supplies the timing grid,
- gliders carry localized state,
- leader structures start and synchronize a sweep,
- ossifiers encode production words and production index behavior,
- data blocks encode the cyclic tag tape,
- collisions delete, pass, regenerate, or append particle packages.

The difficult part is phase. A Cook particle is not just a single row of bits.
It also has an ether phase, spacetime period, horizontal displacement, footprint,
and legal spacing against other particles. A universality-grade construction
needs all of those facts aligned.

## 2. Implementation map

The code is split into named emitters and observers so each physical component
can be audited independently.

### Ether

`cook_ether_emit` in `encoder/cook_construction.c` writes repetitions of the
working width-14 ether word:

```text
00010011011111
```

Tests evolve emitted ether with the local `evaluator/rule110.c` evaluator and
compare it against the expected periodic background.

### Gliders

The catalog has emitters for `A` through `H` plus the glider gun:

- `cook_glider_A_emit`
- `cook_glider_B_emit`
- `cook_glider_C_emit`
- `cook_glider_D_emit`
- `cook_glider_E_emit`
- `cook_glider_F_emit`
- `cook_glider_G_emit`
- `cook_glider_H_emit`
- `cook_glider_gun_emit`

These emitters overlay finite row snippets on the ether background. The current
snippets are best-effort row-0 patterns selected from visual catalog behavior
and direct local Rule 110 simulation. They are intentionally isolated behind
function names so phase tables can replace their templates without changing
callers.

Behavioral tests check localized motion or persistence and far-field ether
preservation. They do not certify Cook-catalog phase identity.

### Collisions

The collision layer simulates selected ordered pairs under one chosen spacing.
The checked matrix covers `A`, `B`, `C`, and `D`, giving 16 ordered pairs.

The observer compares a perturbed row against an independently evolved pure
ether row. It classifies the final difference pattern coarsely:

- `passthrough` when the disturbance island count remains close to the incoming
  particle count,
- `annihilation` when the final row matches the evolved ether control row.

Under the current spacing, all simulated pairs classify as passthrough or
annihilation. No current collision row is a certified productive collision.

### Leader

The leader emitter writes a fixed 20-cell marker over ether. In this scaffold it
marks the start of the active substrate region and gives the empty encoder a
stable disturbance to place. Tests check persistence and far-field ether
preservation, not Cook section 5-6 phase identity.

### Ossifier

The ossifier emitter writes a fixed-width marker per production bit. Logical
`0` and `1` choose different local templates. Empty productions write no
payload. This gives the encoder deterministic production regions, but it does
not certify the production-append interaction after a consumed data `1`.

### Data block

The data-block emitter writes fixed-width slots for cyclic tag tape bits.
Logical `0` and `1` use distinct finite templates, with ether left in the
unused part of each slot. Tests check slot boundaries, distinct encodings, and
ether preservation outside the block. They do not decode evolved Rule 110 rows
back into logical tape symbols.

### `cook_encode`

The public encoder entry point is:

```c
size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap);
```

The implemented path handles the empty cyclic-tag input: no productions and an
empty initial tape. It emits ether plus the current leader marker. Non-empty
cyclic tag inputs return zero bytes. The one-production case is the next
construction boundary.

## 3. Best-effort versus phase-exact

The current layer is best-effort.

Best-effort means:

- emitters are deterministic,
- the output is valid Rule 110 cell data,
- tests run the real local Rule 110 evaluator,
- components are observed behaviorally under bounded evolution,
- names follow Cook's construction vocabulary,
- the code shape preserves a path to phase-exact replacement.

Best-effort does not mean:

- every glider template is the exact Cook 2004 phase,
- every collision product is known,
- leader and ossifier packets are the published construction packets,
- data symbols implement the cyclic tag step rule,
- Rule 110 evolution is proven to simulate every cyclic tag input,
- the Mark theorem manifests are certified through Rule 110.

Phase-exact construction would require machine-readable particle templates for
all relevant phases, exact spacings, exact collision products, and an
observation argument showing that the evolved substrate realizes the cyclic tag
step relation. That is not present yet.

## 4. Manifest relation

The cyclic-tag manifests use `.ct` files. They define production words and
human-readable assertions for the existing Mark theorem tests.

The Rule 110 substrate format uses `.r110` files. A `.r110` manifest stores:

- `INITIAL_PATTERN`,
- `EVOLUTION_STEPS`,
- `EXPECTED_FINAL_PATTERN`.

Each pattern is an ASCII bit string with one Rule 110 cell per character. The
intended runner, `mr_run_r110_manifest`, evolves `INITIAL_PATTERN` for the
declared number of steps and compares the result against
`EXPECTED_FINAL_PATTERN`. A tolerance parameter can be used for explicitly
best-effort Cook tests where small phase uncertainty is part of the test
contract.

At this stage, `.r110` is a substrate-manifest format. It is not a certificate
that a `.ct` manifest has been simulated by Cook's construction.

## 5. Test strategy

The test suite is layered.

Evaluator tests check the Rule 110 local table, boundary convention, and
determinism of row evolution. Ether tests check that the chosen background
behaves consistently under the evaluator.

Glider tests insert each named particle on top of ether. They assert bounded
non-ether disturbance behavior after a fixed number of steps, plus preservation
of far-field ether. These tests are behavioral, not phase certificates.

Leader, ossifier, and data-block tests check deterministic placement and bounded
behavior. They ensure that helper emitters do not corrupt unrelated ether
regions and that logical templates are distinct where required.

Collision tests run the selected pair matrix and classify final difference
islands against an evolved ether control. The classification is coarse on
purpose: it records what the current templates do without pretending to identify
exact particle products.

The empty encoder test verifies that the degenerate cyclic tag input produces
ether plus leader and rejects non-empty inputs at the current construction
boundary. Future encoder tests need to compare cyclic tag tape behavior against
decoded Rule 110 substrate behavior.

## 6. Known limitations

The largest limitation is that the construction has no certified productive
collision path.

Known limitations:

- glider templates are row-0 approximations rather than full phase tables,
- the glider gun is a separated source band, not a certified source oscillator,
- collision classification is limited to 16 ordered `A` through `D` pairs,
- the chosen collision spacing currently yields passthrough or annihilation,
- leader, ossifier, and data block are behavioral substrate encodings,
- production-word append behavior is not implemented,
- non-empty `cook_encode` inputs are not encoded,
- no Rule 110 decoder maps evolved substrate rows back to cyclic tag tape,
- `.r110` manifests document a row format but do not yet certify Mark round-trip
  execution,
- no phase-exact Cook 2004 transcription is present.

These limitations are exactly the gap between a demonstration scaffold and a
universality-grade construction.

## 7. Future work

Future work should narrow the gap in this order.

Phase tables: extract or reconstruct phase-exact templates for the ether, `A`
through `H`, the gun, leader packets, ossifier packets, and data symbols. Each
template should include width, phase, period, displacement, and required
neighboring ether phase.

Productive collisions: build simulation fixtures for construction-critical
collisions. The active machinery must consume data `0` and append nothing,
consume data `1` and append the active production, join appended payload to the
data-block tail, and restore phase for the next production index.

One-production encoder: implement a minimal cyclic tag system with one
production and a short tape. This is the smallest useful end-to-end Cook encoder
target and should include a trace comparison against the direct cyclic tag
evaluator.

General encoder: support multiple productions and arbitrary finite tapes. The
encoder should compute required row length before writing, reserve guard ether,
and keep all package placement constants centralized.

Decoder and manifests: add an observation layer that can recover cyclic tag
tape behavior, or at least the Mark-manifest observables, from evolved Rule 110
rows. Then generate `.r110` manifests from the existing `.ct` manifests and test
them with `mr_run_r110_manifest`.

A true universality claim needs the phase-exact construction, productive
collisions, manifest generation, runner verification, and a documented bridge
from cyclic tag semantics to Rule 110 substrate behavior. Until those pieces
are present, this layer should be described as a behavioral Cook-construction
scaffold.
