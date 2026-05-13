# Cook encoder phase-exact design

This document specifies the Level 3.4 encoder interface and composition plan for
arbitrary cyclic-tag programs. It is a design for the phase-exact path, not a
claim that the current repository can emit Cook's full cyclic-tag emulator.

The active blockers are recorded in `docs/cook_glider_phases.md` and
`docs/cook_phase_exact_components.md`: only the `A(f1_1)=111110` glider phase is
checked, and the phase-exact leader, ossifier, and data-block emitters return
catalog-missing until the `B` through `H` package catalog and component bodies
are available.

## Interface

The stable behavioral encoder remains:

```c
size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap);
```

The phase-exact entry point is:

```c
int cook_encode_phase_exact(const CyclicTagInput *ct,
                            uint8_t *out,
                            size_t out_cap,
                            size_t *written_out);
```

Return statuses:

- `COOK_ENCODE_PHASE_EXACT_OK`: the row was emitted.
- `COOK_ENCODE_PHASE_EXACT_CATALOG_MISSING`: the layout is valid, but the Cook
  phase catalog or component bodies are unavailable.
- `COOK_ENCODE_PHASE_EXACT_INVALID_INPUT`: the cyclic-tag input is malformed.
- `COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER`: `out_cap` is too small;
  `*written_out` is the required cell count.
- `COOK_ENCODE_PHASE_EXACT_LAYOUT_OVERFLOW`: size arithmetic overflowed.

In the default build, `cook_encode_phase_exact` computes the layout and returns
`COOK_ENCODE_PHASE_EXACT_CATALOG_MISSING` before writing to `out`. This mirrors
the component-level phase-exact entry points.

## Coordinate model

The encoder uses one absolute cell coordinate system over a row pre-filled with
Cook ether. Every position is an offset from cell zero. Every package origin is
rounded to a `COOK_ETHER_WIDTH` boundary unless the future catalog explicitly
requires a different ether phase.

The current structural layout is:

```text
left guard
leader
leader-to-ossifier gap
P ossifier origins at fixed stride L
ossifier-to-data gap
N data-symbol origins at fixed stride K
right guard
```

These constants are deliberately named as phase constants. The present C stub
uses conservative ether-period multiples only to make the composition logic
auditable. The final numeric values must come from checked Cook package data.

## Tape encoding

For an initial tape of `N` bits, the phase-exact encoder lays out `N` data
symbol packages. The logical bit at index `j` is placed at:

```text
data_pos(j) = data_base + j * K
```

where `K` is the data-symbol stride in cells. Conceptually:

```text
K = data_symbol_period * ether_spatial_period
```

The exact `data_symbol_period` is blocked on the data-block package catalog. It
must be large enough that neighboring symbol light cones do not interact before
the head symbol is consumed, and it must match the tail-append phase so payload
gliders released by an active ossifier land on legal future symbol origins.

The current stub composes tape symbols by calling:

```c
cook_data_block_emit_phase_exact(out, data_pos(j), total, bit_j, 1);
```

for each symbol. When the data-block body lands, this per-symbol call shape can
remain if the body treats a one-bit block as one package. If the checked catalog
requires a multi-symbol wrapper or tail marker, the layout layer should keep
the public API unchanged and replace the internal data-region emitter.

## Production encoding

For `P` productions, the phase-exact encoder lays out `P` ossifier packages in
cyclic order. Production `i` is placed at:

```text
ossifier_pos(i) = first_ossifier_pos + i * L
```

where `L` is the ossifier stride in cells. Conceptually:

```text
L = ossifier_clock_period * ether_spatial_period
```

`L` must preserve the clock packet phase between adjacent productions. It must
also exceed the maximum emitted footprint of any production package:

```text
L >= max_i ossifier_width(production_i) + right_guard_for_clock_lane
```

The current stub computes a conservative stride from the maximum production
width reported by the behavioral component constants, rounds it to an ether
boundary, and adds an ether-period guard. The final value must be replaced by
the checked ossifier pass-through timing.

Each production package is planned through:

```c
cook_ossifier_emit_phase_exact(out,
                               ossifier_pos(i),
                               total,
                               production_i_bits,
                               production_i_len);
```

The ossifier body must encode three behaviors:

- inactive pass-through restores the clock packet for production `i + 1`,
- active collision with data `0` consumes the head and appends nothing,
- active collision with data `1` releases the production payload.

## Glider gun placement

Cook's construction uses periodic packages that supply the active particles
driving the leader, production selection, and data-symbol collisions. The
phase-exact encoder treats the gun as a clock source attached to the leader
region, not as a decorative row prefix.

The required catalog facts are:

```text
gun_pos = leader_pos + gun_origin_delta
gun_period = checked emission period in generations
gun_to_first_data_time = checked collision generation
gun_to_first_data_delta = first_data_pos - gun_pos
```

The first emitted active packet must meet the first data symbol at the same
generation and ether phase as the first active ossifier packet. That condition
links the three layout equations:

```text
leader_to_first_ossifier_phase(leader_pos, first_ossifier_pos)
ossifier_to_first_data_phase(first_ossifier_pos, data_base)
gun_to_first_data_phase(gun_pos, data_base)
```

The current C path does not call a phase-exact glider-gun emitter because the
public construction header only exposes the checked `A` phase and the component
contracts do not yet define gun placement. When the catalog lands, the
composition function should add the gun after ether emission and before
leader/ossifier/data writes, so catalog-missing remains an all-or-nothing
pre-write status.

## Leader-tape interface

The leader is the synchronization origin for the first sweep. Its right-side
outgoing clock lane must reach the first ossifier before the data-head collision
window, and the first active data collision must target `data_pos(0)`.

The required checked relation is:

```text
leader_pos + leader_to_ossifier_delta = first_ossifier_pos
first_ossifier_pos + ossifier_to_data_delta = data_pos(0)
```

Those deltas are package facts, not arbitrary padding. The current stub names
them as ether-period gaps and keeps them isolated in the layout planner so the
future catalog can replace the numeric constants without changing callers.

## Resource accounting

Let:

- `N` be the initial tape length,
- `P` be the production count,
- `W_L` be the leader package footprint,
- `W_O(i)` be the package footprint for production `i`,
- `W_D` be one data-symbol footprint,
- `G_left` and `G_right` be boundary guards,
- `G_LO` be the leader-to-first-ossifier gap,
- `G_OD` be the last-ossifier-to-data gap,
- `K` be the data-symbol stride,
- `L` be the ossifier stride.

The minimum row length is:

```text
leader_end = G_left + W_L
first_ossifier = round_ether(leader_end + G_LO)
ossifier_end =
  first_ossifier                                  if P = 0
  first_ossifier + (P - 1) * L + max_i W_O(i)     otherwise
data_base = round_ether(ossifier_end + G_OD)
data_end =
  data_base                                      if N = 0
  data_base + (N - 1) * K + W_D                  otherwise
total = round_ether(data_end + G_right)
```

This is a spatial lower bound for the emitted row. A complete `.r110` manifest
also needs a time horizon and enough guard ether that boundary effects cannot
reach the observed window before that horizon.

## Verification chain

The phase-exact encoder can return `OK` only after these upstream facts exist:

1. `B` through `H` glider phases are checked against local Rule 110 evolution.
2. The glider gun has a checked emission period and output phase.
3. `cook_leader_emit_phase_exact` emits a checked leader package.
4. `cook_ossifier_emit_phase_exact` emits checked production packages.
5. `cook_data_block_emit_phase_exact` emits checked data-symbol packages.
6. Direct simulations validate leader-to-ossifier, inactive ossifier
   pass-through, active data `0`, active data `1`, and tail-append collisions.

Until then, the entry point is intentionally structural: it validates inputs,
computes the future composition layout, reports required capacity, and returns
the catalog-missing sentinel without modifying the caller's buffer.
