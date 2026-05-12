# M2 Notes

Glider A is emitted as the row-0 visual-catalog approximation `1011` over a pre-filled ether background. Cook's published catalog identifies A as a period-(3,2) particle, but the implementation here does not yet encode a phase-exact multi-row placement table. The current test therefore verifies a moving localized perturbation and preservation of far-field ether, not exact Cook-catalog phase identity.

Glider B is emitted as the row-0 best-effort perturbation `101` over phase-0 ether. This pattern was chosen because direct Rule 110 simulation produces a compact left-moving disturbance relative to the ether phase. The source diagrams were not available in this worktree, so the test is behavioral and does not certify exact Cook-catalog phase identity.

Glider C is emitted as the row-0 best-effort perturbation `1001` over phase-0 ether. This pattern produces a wider moving disturbance while leaving the right-side far-field ether intact in the tested window. It is a speculative visual-catalog seed, not a phase-exact transcription of Cook 2004 Figure 4.

Glider D is emitted as the row-0 best-effort perturbation `11010` over phase-0 ether. In direct simulation it contracts to a compact left-moving defect and preserves far-field ether in the tested window. As with B and C, this is a behavioral placeholder pending primary-source phase data.

Gliders E, F, G, and H use single-row visual-catalog approximations cross-checked against Cook 2004 section 3 and secondary Rule 110 glider catalogs. The selected rows are respectively `111001`, `1100101`, `111000100111`, and `10110100101110` over the Cook ether phase. The tests assert localized motion after 100 Rule 110 steps and ether preservation outside the perturbation light cone.

The glider gun emitter is represented by a 518-cell source band made from separated E/F/G/H row approximations at 168-cell ether-compatible spacing. It is not a phase-exact Cook source oscillator; the test records that the band produces multiple separated mobile perturbations after 500 Rule 110 steps while leaving far-field ether unchanged.

## Design phase observations

Cook's construction makes the existence and high-level role of the productive collision families clear: leader, ossifier, and data-block packages interact so that a consumed `0` appends nothing and a consumed `1` appends the active cyclic-tag production. The exact low-level `A`-through-`H` all-pairs collision outcomes are not firmly established from accessible prose summaries alone. They should be treated as conjectural until direct local Rule 110 simulation verifies phase, spacing, transient cleanup, and outgoing products.

Before Phase B and C implementation can be trusted, the project still needs primary-diagram or simulation-derived templates for the leader package, each ossifier package, and the data-block encodings for logical `0` and `1`. The encoder design should therefore keep those structures behind named emitters and expose phase/separation metadata in collision tests rather than hard-coding a phase-free glider-pair table.

## Cook collision simulation observations

The current collision simulator uses a pure ether control row evolved for the same number of Rule 110 steps, then classifies the perturbed row by counting islands that differ from that control. The exploratory table below uses positions `420` and `560` with `220` evolution steps. These rows are deterministic observations for the current row-0 `A`/`B`/`C`/`D` emitters and this spacing; they are not phase-exact Cook 2004 collision products.

| Left | Right | Outcome | Interpretation |
| --- | --- | --- | --- |
| `A` | `A` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `A` | `B` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `A` | `C` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `A` | `D` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `B` | `A` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `B` | `B` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `B` | `C` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `B` | `D` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `C` | `A` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `C` | `B` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `C` | `C` | `annihilation` | The final row matches the evolved ether control row in the full simulated window. |
| `C` | `D` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `D` | `A` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `D` | `B` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `D` | `C` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |
| `D` | `D` | `passthrough` | The final perturbation island count is close to the initial two-particle count. |

Classification remains intentionally coarse. A `passthrough` row means only that the post-window island count is approximately conserved by this heuristic. It does not certify outgoing particle identities, exact velocities, or phase restoration. A row classified as `annihilation` means the simulated row is equal to the separately evolved ether row at the end of the chosen window.

## Leader observations (B3)

The leader emitter uses a 20-cell row-0 overwrite `10111111010100001100` on a pre-filled Cook ether background. This pattern was selected by direct local Rule 110 simulation because it leaves detectable non-ether structure in the injection window after 500 steps and keeps far-field ether phase-aligned after 100 steps. It is a behavioral marker for the M2 construction scaffold, not a phase-exact transcription of Cook 2004 section 5.

## Ossifier observations (B4)

The ossifier emitter uses a fixed 30-cell overwrite per production bit. Logical `0` and `1` select distinct local perturbation templates over the Cook ether, and an empty production writes nothing. This is a behavioral encoding of production-word width and persistence only; it does not certify Cook 2004 section 5 phase identity, production-index timing, or the data-block collision that appends bits after a consumed `1`.

## Data block observations (B5)

The Cook data-block emitter uses a fixed 50-cell slot per cyclic-tag tape bit. Logical `0` is represented by an 18-cell sparse marker and logical `1` by a 28-cell wider marker, both over pre-filled ether; the unwritten tail of each slot remains ether and supplies separation between adjacent logical symbols. This is a best-effort behavioral tape overlay, not a phase-exact Cook 2004 section 6 data block. The current test verifies fixed-width perturbation bounds and phase-preserving ether outside the block, but it does not certify productive ossifier collisions or tape-tail extension.

## Empty cyclic-tag encoder observations (C2)

The empty cyclic-tag encoder emits 50 periods of Cook ether and overlays the current leader marker at cell 100. Because this row is only 700 cells wide, the 500-step check compares against a separately evolved pure-ether row with the same finite zero-boundary evaluator. The observed difference is therefore attributed to the leader marker rather than to boundary phase drift. Non-empty cyclic-tag inputs remain outside the C2 envelope and return zero bytes.

## One-production cyclic-tag encoder observations (C3)

The one-production encoder uses a fixed M2 layout over Cook ether: leader at cell 100, the single ossifier at cell 300, and an optional initial data block at cell 800. The substrate is padded to at least 220 ether periods, with additional trailing ether when a longer tape requires it, so the 1000-step behavioral check has guard space beyond the data block. The C3 test verifies initial perturbations in the leader, ossifier, and data-block regions, preserves ether in the gaps between them, and confirms each populated region still differs from a same-step ether control after 1000 Rule 110 steps. This remains a structural persistence check for the current best-effort templates, not a proof of productive cyclic-tag simulation.

## Arbitrary cyclic-tag encoder observations (C4)

The arbitrary encoder path accepts any production count, including the Mark enum shape with zero productions and a non-empty tape. For two or more productions it lays out Cook ether, a leader at cell 100, one ossifier per production starting at cell 300, and an optional data block after the production list. Ossifier start positions are separated by at least 200 cells, with longer productions expanding their local stride before the next ossifier. The C4 test covers two-production, four-production, and all eight Mark manifest production lists. This is a structural substrate test only; productive Rule 110 collisions and cyclic-tag execution equivalence remain outside the current checkpoint.
