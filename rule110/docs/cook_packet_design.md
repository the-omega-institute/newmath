# Cook packet phase-exact layout

This note describes the packet emitters used by the current phase-exact Cook
encoder path.

The source data is the Martinez phase catalog registered in
`encoder/glider_phases.c` plus the collision spacings recorded in
`encoder/martinez_2012_collisions.txt`. Distances written as `n e` are encoded
as `n` Cook ether tiles, with one ether tile equal to 14 cells.

## Ossifier

`cook_ossifier_emit_phase_exact` emits two groups of packed `A^4` packets.
Each packed `A^4` uses the machine-110 row word `0001110111`. A group contains
four packed `A^4` words. The two groups are separated by `(6k + 5)` ether
tiles.

The public ABI still accepts a production bit pointer and length. The first
bit selects a conservative spacing class for this pass: `0` maps to `k = 0`
and `1` maps to `k = 1`. The emitter returns catalog-missing without writing
when the output row is not a binary Rule 110 row or the packet footprint does
not fit.

## Data block

`cook_data_block_emit_phase_exact` emits one tape symbol as four `C2(A, f1_1)`
catalog phases. Logical `Y` uses spacings
`C2^18 C2^18 C2^14 C2`. Logical `N` uses
`C2^28 C2^10 C2^14 C2`.

The existing ABI accepts a tape pointer and length. The first tape bit selects
the symbol: nonzero is `Y`, zero is `N`.

## Leader

`cook_leader_emit_phase_exact` emits eight `Ebar(A, f1_1..f4_1)` gliders
followed by four `C2(A, f1_1..f4_1)` gliders. The local soliton table contains
the construction-relevant `C2(A, f1_1)-3 e-Ebar(C, f1_1)` spacing; this pass
uses a three-ether-tile separation for the leader packet lanes.

The result is a phase-catalog packet composition, not a completed proof of the
Cook leader's acceptor/rejector collision behavior.

## Encoder pass

`cook_encode_phase_exact` now composes actual phase-exact component emitters:

1. Cook ether background.
2. Leader packet after the left guard.
3. One ossifier packet per production.
4. One data-block packet per initial tape symbol.
5. Trailing ether guard.

The first smoke test covers a simple non-empty cyclic-tag shape with one
production and one tape symbol. It checks that component footprints compose
without overlap, survive 100 Rule 110 steps as localized non-ether structure,
and leave far-field ether windows intact.

This is packet-layout evidence only. It does not claim cyclic-tag round-trip
execution, production append correctness, or a decoded universal computation.
