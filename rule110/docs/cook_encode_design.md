# Cook encoder design notes

This note prepares Phase C: translating a cyclic tag system into a Rule 110
initial row using Cook's construction. It describes the target structure and the
algorithmic shape of `cook_encode`; it does not define final bit patterns for
leader, ossifier, or data packages.

## Sources and trust posture

Primary source:

- Matthew Cook, "Universality in Elementary Cellular Automata", Complex Systems
  15(1):1-40, 2004:
  <https://wpmedia.wolfram.com/sites/13/2018/02/15-1-1.pdf>. Sections 5 and 6
  are the direct source for the cyclic tag system construction.

Secondary sources:

- Genaro J. Martinez, Harold V. McIntosh, Juan C. Seck-Tuoh-Mora, and Sergio V.
  Chapa-Vergara, "Reproducing the cyclic tag system developed by Matthew Cook
  with Rule 110 using the phases fi_1": <https://arxiv.org/abs/1307.7951>.
- Stephen Wolfram, A New Kind of Science, notes around page 1116:
  <https://www.wolframscience.com/nks/notes-11-8--initial-conditions-for-rule-110/>,
  for the rough scale estimate that cyclic tag system symbols require thousands
  of Rule 110 cells in Cook-style encodings.
- Wikipedia, "Rule 110": <https://en.wikipedia.org/wiki/Rule_110>, for a
  concise secondary summary of Rule 110 universality through cyclic tag systems.

Exact particle phases and spacings should be considered untrusted until
confirmed by direct local Rule 110 simulation.

## Goal

The translator takes a finite cyclic tag system and emits a finite Rule 110
substrate row. Under Rule 110 evolution, that row should simulate the cyclic tag
system's tape evolution.

At this milestone the target is practical rather than fully general:

- produce `.r110` manifests for the eight existing Mark cyclic tag manifests,
- preserve a clear path to arbitrary cyclic tag systems,
- keep all low-level Cook phase decisions isolated behind named emitters,
- make collision verification observable through existing Rule 110 tests.

## Inputs

The input is a cyclic tag system:

- `num_productions`: number of productions in cyclic order,
- `productions[i]`: finite bit word appended when the consumed symbol is `1`,
- `initial_tape`: finite bit word present before the first step,
- optional execution bound or expected observable trace supplied by the manifest.

The existing C type is expected to be `CyclicTag`, already used by the
groundcompiler-facing evaluator. The Cook encoder should not reinterpret the
logical cyclic tag semantics. It only chooses a Rule 110 substrate representing
the same program and initial tape.

Logical cyclic tag step:

1. Read and delete the first tape symbol.
2. If it is `1`, append the current production word.
3. If it is `0`, append nothing.
4. Advance the production pointer cyclically.
5. Halt or become empty if the tape has no symbols, depending on manifest
   semantics.

## Output

The output is a finite bit pattern for a Rule 110 initial state:

- `out`: caller-provided byte buffer containing `0` and `1` cell values,
- `out_len`: number of valid cells emitted,
- far-field assumption: cells outside `[0, out_len)` are ether-compatible or are
  padded by the manifest runner with ether.

The generated row should include enough leading and trailing ether that early
collisions do not touch artificial boundaries during the intended manifest
execution window.

The `.r110` manifest format can remain simple for M2:

- a header with source CT name and expected simulation steps,
- one ASCII bit row or a compact run-length row if size becomes too large,
- optional comments documenting the Cook encoder version and padding.

## Structural elements

Cook's construction is not a direct "one bit becomes one cell" encoding. It is a
carefully phased particle machine over the Rule 110 ether.

### Ether background

Ether is the periodic background on which all particles travel. The existing
Phase A code records the row word `00010011011111` as a working ether period.
All leader, ossifier, and data packages must be placed on an ether-compatible
phase.

Encoder responsibilities:

- emit enough ether periods for the whole construction,
- expose a coordinate system in cells,
- align all package emitters to the same ether phase,
- preserve guard ether at both row boundaries.

### Leader

The leader is the marker structure that starts the computation. Conceptually it
is the clocking and synchronization package for the simulated cyclic tag system.
It identifies where the first active sweep begins and determines when the first
ossifier is encountered.

Expected implementation shape:

- a named `cook_leader_emit` helper,
- one or more phase templates,
- a required ether phase,
- a documented bounding box,
- a post-emission test that verifies the package evolves stably until it reaches
  the first ossifier.

Open detail: Cook's exact leader bit pattern must be extracted from sections
5-6 diagrams or from a phase reconstruction source.

### Ossifiers

Ossifiers encode the cyclic list of productions. There is one ossifier per
production, in cyclic order. During computation, the active interaction between
the clock/leader package, the data block, and the current ossifier determines
whether the production word is appended.

For a production `p_i`, the ossifier must encode:

- position in the cyclic production order,
- the emitted word for a consumed `1`,
- a no-op path for a consumed `0`,
- phase restoration for the next production.

Expected implementation shape:

- `cook_ossifier_emit(out, pos, production_bits, production_len, phase)`,
- a spacing rule `ossifier_pos(i)`,
- per-production width estimates,
- a collision test against data bit `0`,
- a collision test against data bit `1`,
- a pass-through or cycle-advance test to the next ossifier.

Open detail: exact bit templates for production words are the main research
blocker for Phase C.

### Data block

The data block encodes the current cyclic tag tape. It is not merely a raw bit
string; each logical symbol becomes a package of particles separated so that
Cook's collisions consume the head and append new tail symbols at the correct
time.

For each tape bit:

- `0` must collide with the active production machinery and append nothing,
- `1` must collide with the active production machinery and append the current
  production word,
- adjacent symbols must remain distinguishable until consumed,
- tail extension must preserve the data-block phase convention.

Expected implementation shape:

- `cook_data_block_emit(out, pos, tape_bits, tape_len, phase)`,
- `cook_data_symbol_width(bit)` or a fixed cell stride,
- a tail marker or spacing region if required by Cook's diagrams,
- a decoder/debug view that maps evolved particle packages back to tape symbols.

Open detail: the exact data-symbol package is not yet available in local code.

## Coordinate model

Use a single absolute cell coordinate system over the output row:

- cell `0` is the first emitted cell,
- all structure positions are absolute cell offsets,
- helper functions accept both target position and available output length,
- helper functions return the written span or fail with required length.

The encoder should compute layout before writing:

1. Estimate package widths.
2. Estimate required gaps and guard ether.
3. Compute total substrate length.
4. If `out == NULL` or capacity is too small, report required length through
   `out_len` without writing.
5. Emit ether across the full span.
6. Overlay leader, ossifiers, and data block in phase-compatible positions.

This two-pass shape avoids buffer overflows and lets manifest generation ask for
size before allocation.

## High-level API

Planned C signature:

```c
int cook_encode(const CyclicTag *ct, uint8_t *out, size_t *out_len);
```

Recommended return values:

- `0`: success,
- nonzero invalid-input or insufficient-buffer code,
- `*out_len` always set to required or written length when possible.

The encoder should reject:

- null `ct`,
- null `out_len`,
- unsupported symbol values outside `0` and `1`,
- production count zero unless an explicit empty-program convention is defined,
- layouts that overflow `size_t`.

## Pseudocode

```text
cook_encode(ct, out, out_len):
  validate ct and out_len

  layout = cook_layout_plan(ct)
  if layout overflows:
    return error

  required_len = layout.total_cells
  if out is null or *out_len < required_len:
    *out_len = required_len
    return insufficient_buffer

  emit_ether(out, layout.ether_period_count)

  inject_leader(out, layout.leader_pos)

  for i in 0..ct->num_productions-1:
    inject_ossifier(
      out,
      layout.ossifier_pos[i],
      ct->productions[i].bits,
      ct->productions[i].len)

  inject_data_block(
    out,
    layout.data_block_pos,
    ct->initial_tape.bits,
    ct->initial_tape.len)

  *out_len = required_len
  return success
```

The real implementation should use named helpers rather than embedding Cook
templates directly in `cook_encode`. That keeps the translator readable and
lets Phase B collision tests target individual packages.

## Layout planning

Initial layout can be conservative:

- leading guard ether: at least 64 ether periods,
- leader region,
- gap to first ossifier,
- one ossifier region per production,
- gap from last ossifier to data block,
- data block region,
- trailing guard ether sized to the expected run horizon.

The final Cook construction may require interleaving leader, ossifiers, and data
block in a more specific spacetime arrangement. The planning layer should hide
that detail behind `cook_layout_plan` so the public `cook_encode` signature does
not churn.

## Size estimate

Wolfram's NKS notes around page 1116 describe Cook-style cyclic-tag-system
encodings as requiring roughly thousands of Rule 110 cells per cyclic tag system
symbol. For planning, use:

- about 3000 Rule 110 cells per logical CT symbol,
- plus fixed overhead for leader, production list, and guard ether,
- plus growth margin for manifest execution steps.

The eight Mark manifests are small cyclic tag systems. Expected `.r110` manifest
size:

- lower bound: roughly 10 KB for tiny tapes and short production lists,
- normal expected range: 10-100 KB each,
- possible upper range: hundreds of KB if we keep generous guard ether or use
  uncompressed ASCII rows.

If any manifest exceeds 10 MB, switch the `.r110` format to RLE or add an RLE
variant before committing generated outputs.

## Verification plan

Phase C should not rely on end-to-end manifest success alone. Verification
should be layered:

1. Ether tests: emitted background remains periodic under Rule 110 evolution.
2. Package tests: leader, ossifier, and data symbol packages each evolve as
   expected in isolation.
3. Collision tests: active package collisions reproduce Cook's logical effects.
4. One-production CT test: a minimal cyclic tag system behaves as predicted.
5. Mark manifest tests: each existing Mark CT manifest has matching observable
   behavior between the CT evaluator and Rule 110 evolution.

The decoder used in tests can be partial. It only needs to observe the logical
tape behavior required by the Mark manifests, not reconstruct arbitrary Cook
spacetime diagrams.

## Error handling and determinism

The encoder should be deterministic:

- same CT input produces byte-identical Rule 110 output,
- no random phase choices,
- no dependence on pointer addresses or platform endianness,
- all layout constants centralized in the Cook construction module.

Errors should be reported before partial writes whenever possible. In
insufficient-buffer mode, the caller's `out` contents should be treated as
undefined unless the function explicitly guarantees no write.

## Open questions

- Exact leader template: not yet extracted from Cook's section 5-6 diagrams.
- Exact ossifier template: main blocker for arbitrary production encoding.
- Exact data `0` and `1` symbol packages: needed before meaningful CT
  round-trip tests can pass.
- Phase alignment: all templates must share an ether phase convention.
- Decoder strategy: we need a practical way to recover logical tape symbols from
  evolved Rule 110 rows for tests.
- Boundary convention: `.r110` manifests need to specify whether cells outside
  the stored finite row are ether, zero, or runner-padded.
- Empty tape behavior: confirm how existing Mark CT manifests define halted or
  empty-tape states before mapping them to Rule 110 observation.
- Compression threshold: decide whether large `.r110` rows stay plain ASCII or
  use RLE.

## Implementation checkpoints for Phase C

- `C2`: empty or degenerate CT emits ether plus leader and passes stability
  tests.
- `C3`: one-production CT emits a single ossifier and passes a small logical
  trace comparison.
- `C4`: arbitrary CT layout supports all existing Mark manifests.
- `C5`: generated `.r110` files include enough metadata and padding to be
  reproducible by the manifest runner.

These checkpoints depend on Phase B's collision and package tests. Without
verified leader, ossifier, and data block collisions, `cook_encode` should remain
behind an explicit experimental or unsupported status.
