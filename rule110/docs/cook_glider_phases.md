# Cook glider phase status

This page records the Level 3.1 phase work. The target is to replace
single-row visual approximations with phase-checked Rule 110 words. This file
certifies only glider A. Gliders B-H remain best-effort emitters.

## Sources checked

Primary Cook Figure 4 is not present in this worktree as machine-readable
data. This work does not transcribe pixels from an unavailable figure.

The usable source is the arXiv source bundle for Martinez, McIntosh, Seck Tuoh
Mora, and Chapa Vergara, "Determining a regular language by glider-based
structures called phases f_i_1 in Rule 110" (`arXiv:0706.3348`). Its LaTeX
source gives the phase-language words for A and B and states that A moves two
cells to the right in three generations.

The source gives these A phase words in Ph_1:

```text
A(f1_1) = 111110
A(f2_1) = 11111000111000100110
A(f3_1) = 11111000100110100110
A(f4_1) = A(f1_1)
```

## Glider A result

`cook_glider_A_emit` emits `A(f1_1) = 111110`.

The test suite verifies the local periodic orbit for that phase word under
Rule 110 with periodic boundary conditions:

```text
t=0: 111110
t=1: 100011
t=2: 100110
t=3: 101111
```

The row at `t=3` is the `t=0` word shifted two cells to the right on the
six-cell periodic domain. This matches the documented A velocity `2/3`.

The emitter test also verifies that `cook_glider_A_emit` writes the documented
phase word into the ether-backed row, and the bounded motion tests still check
localized disturbance behavior in the project evaluator.

## B-H status

B-H are not certified here. The same Martinez source includes a B phase list,
but Cook Level 3.1 asks for phase-exact A-H patterns from Cook Figure 4, and
B-H require separate validation against the construction phase conventions and
existing emitter contracts. Copying secondary-source strings without that
validation would overstate the result.

| Glider | Status |
|---|---|
| A | Phase word `A(f1_1)=111110` emitted and period/shift verified. |
| B | Secondary-source phase words found; not emitted. |
| C | Not derived. |
| D | Not derived. |
| E | Not derived. |
| F | Not derived. |
| G | Not derived. |
| H | Not derived. |

## Remaining obstruction

This is not a full Cook 2004 Figure 4 transcription. The exact multi-row finite
particle masks and all Cook construction phases still need direct figure access
or a trusted machine-readable phase catalog. The present certificate covers
only the glider A phase word that can be independently validated by the local
Rule 110 evaluator.
