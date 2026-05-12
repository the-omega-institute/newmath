# Cook phase-exact component contracts

This page records the component-level contract for the Cook leader, ossifier,
and data-block packages. It is a structural specification for the phase-exact
entry points in `encoder/cook_leader.c`, `encoder/cook_ossifier.c`, and
`encoder/cook_data_block.c`.

The underlying phase catalog is not complete. `docs/cook_glider_phases.md`
certifies only the `A(f1_1)=111110` phase. `B` through `H`, package-level
spacings, and construction-critical collision products are unavailable in this
worktree, and `docs/cook_collision_table.md` therefore records package
interactions as pending. The C phase-exact entry points return a catalog-missing
status until those inputs are present.

Primary source: Matthew Cook, "Universality in Elementary Cellular Automata",
Complex Systems 15(1):1-40, 2004, sections 5 and 6. Those sections describe
the cyclic-tag-system emulator using particle packages over Rule 110 ether.

## Common phase contract

Every phase-exact package must be defined by more than a row-0 bit string.

Required fields:

- ether phase at the left and right boundary,
- package width in cells at the emitted row,
- generation phase of each constituent glider,
- horizontal offset of each constituent glider from the package origin,
- legal guard ether before and after the package,
- interaction target, separation, and generation window for each productive
  collision.

The output row must be pre-filled with Cook ether. A phase-exact emitter may
only overwrite the cells inside its declared package footprint. If the catalog
is unavailable or the requested package is outside the buffer, the phase-exact
entry point must return nonzero before writing.

An off-by-one cell placement is not a cosmetic error. Rule 110 particles are
phase objects; shifting a package by a cell, or using the wrong row of a
multi-row phase, changes the time and ether alignment at which collisions
occur. The usual failure modes are a missed collision, a wrong outgoing
particle, persistent unmatched debris, or a clock packet that reaches the next
component in the wrong production phase.

## Leader

### Role

The leader starts the active computation sweep for the cyclic tag emulator. It
marks the synchronization origin, carries the clocking information that selects
the first production, and prepares the first leader-ossifier interaction.

The current behavioral `cook_leader_emit` writes a 20-cell marker. That marker
is useful for bounded substrate tests, but it is not the Cook leader package.
The phase-exact entry point is `cook_leader_emit_phase_exact`.

### Constituents

The leader depends on a checked `A` phase for the visible leading signal and on
supporting package gliders from the `B` through `H` families. The precise
variant list, row phases, and offsets must come from Cook section 5-6 diagrams
or from a trusted machine-readable phase catalog, then be replayed through the
local Rule 110 evaluator.

Required decomposition records:

- `A` head or synchronizing signal phase,
- `B`/`C` support particles that establish the first interaction lane,
- `D`/`E`/`F` cleanup or regeneration particles where the construction uses
  them,
- any wider `G`/`H` support particles if present in the package diagram,
- absolute offsets from the leader origin to the first ossifier target.

### Spacing and phase constraints

The leader must be placed on an ether boundary that matches the first ossifier's
incoming interaction phase. Its right guard must be large enough that no support
particle touches the ossifier before the intended generation. Its left guard
must preserve far-field ether for the active sweep.

The first productive check is:

```text
leader package + first ossifier package -> active production clock packet
```

Acceptance requires direct simulation showing the isolated leader package
evolves as cataloged, then reaches the first ossifier with the recorded phase.

### Phase-error impact

If the leader is shifted by `N` cells or emitted at the wrong generation phase,
the first ossifier sees the wrong incoming packet. A small phase error can make
the emulator skip the first production, start in the wrong production index, or
produce debris that corrupts the data-block lane before the first tape symbol is
processed.

## Ossifier

### Role

Ossifiers encode the cyclic list of productions. There is one ossifier package
per cyclic-tag production. During a computation sweep, the active clock packet
passes the inactive ossifiers and interacts with the current ossifier to decide
what payload is released when the head data symbol is `1`.

The current behavioral `cook_ossifier_emit` writes a fixed 30-cell marker per
production bit. It gives tests deterministic substrate regions but does not
certify the production-append mechanism. The phase-exact entry point is
`cook_ossifier_emit_phase_exact`.

### Constituents

An ossifier is a production packet, not an array of raw bit cells. Its
constituent gliders are expected to use the construction-relevant `B`, `C`,
`D`, `E`, and `F` families, with possible wider support from `G` and `H`
depending on the exact Cook package diagram.

Required decomposition records:

- per-production header or phase-restoration packet,
- per-bit package for logical `0`,
- per-bit package for logical `1`,
- spacing from one bit package to the next,
- outgoing payload particles released by a consumed data `1`,
- no-op or cleanup path used by a consumed data `0`,
- spacing from this ossifier to the next ossifier in cyclic order.

### Spacing and phase constraints

The ossifier layout must preserve three independent alignments:

- the leader or clock packet must reach each ossifier in the correct production
  phase,
- the active ossifier must meet the head data symbol in the phase that
  distinguishes data `0` from data `1`,
- emitted production payloads must reach the data-block tail at the same symbol
  spacing used by existing data symbols.

Construction-critical simulations:

```text
clock packet + inactive ossifier -> clock packet for next ossifier
clock packet + active ossifier + data 0 -> head consumed, no payload appended
clock packet + active ossifier + data 1 -> head consumed, production payload released
```

### Phase-error impact

If an ossifier bit package is phase-shifted by `N` cells, the emitted payload no
longer lands in the data tail slot assigned to that bit. A header phase error
can also turn an inactive pass-through into an active interaction, which changes
the cyclic production pointer. Either error breaks the cyclic tag semantics
even if every local row still looks like a bounded Rule 110 disturbance.

## Data block

### Role

The data block encodes the cyclic tag tape. Each logical tape symbol is a
particle package. The head symbol is consumed by the active production
machinery, and newly emitted production symbols are appended at the tail with
the same spacing convention.

The current behavioral `cook_data_block_emit` writes fixed 50-cell slots with
different local templates for logical `0` and `1`. It preserves deterministic
placement but does not define Cook data-symbol packages. The phase-exact entry
point is `cook_data_block_emit_phase_exact`.

### Constituents

Data-symbol packages are expected to use `B` through `H` family particles and
must be compatible with the active ossifier's incoming lanes. The exact `0` and
`1` packages must be taken from the Cook construction diagrams or a verified
phase catalog.

Required decomposition records:

- logical `0` symbol package,
- logical `1` symbol package,
- fixed symbol stride or explicit per-symbol offsets,
- head-consumption collision window,
- tail-append collision window,
- phase-restoration rule after an appended symbol joins the tape.

### Spacing and phase constraints

Adjacent symbols must be far enough apart that their transient light cones do
not merge before the head is consumed, but close enough that the tail-append
payload joins the next legal symbol position. The symbol stride must therefore
be a phase fact, not just a buffer-layout constant.

Construction-critical simulations:

```text
active ossifier + data 0 -> delete head, append nothing
active ossifier + data 1 -> delete head, append current production
production payload + data tail -> stable data-symbol packages at legal stride
```

### Phase-error impact

If a data symbol is emitted at the wrong phase, a logical `0` can behave like an
unclassified package instead of the no-append path, and a logical `1` can fail
to release the active production. Tail phase errors are especially harmful:
they may appear only after several simulated cyclic-tag steps, when appended
symbols are consumed at a different phase than the original tape symbols.

## C entry-point status

The phase-exact APIs are present so the replacement path is mechanical:

- `cook_leader_emit_phase_exact`
- `cook_ossifier_emit_phase_exact`
- `cook_data_block_emit_phase_exact`

With the default build, each returns its component's
`*_PHASE_EXACT_CATALOG_MISSING` status and does not modify the output buffer.
Defining `COOK_PHASE_EXACT_BH_AVAILABLE` is reserved for a checked catalog that
contains the `B` through `H` phase masks, package spacings, and the direct
simulation evidence needed by these components.
