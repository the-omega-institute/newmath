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
