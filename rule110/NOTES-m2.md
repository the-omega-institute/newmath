# M2 Notes

Glider A is emitted as the row-0 visual-catalog approximation `1011` over a pre-filled ether background. Cook's published catalog identifies A as a period-(3,2) particle, but the implementation here does not yet encode a phase-exact multi-row placement table. The current test therefore verifies a moving localized perturbation and preservation of far-field ether, not exact Cook-catalog phase identity.

## Design phase observations

Cook's construction makes the existence and high-level role of the productive collision families clear: leader, ossifier, and data-block packages interact so that a consumed `0` appends nothing and a consumed `1` appends the active cyclic-tag production. The exact low-level `A`-through-`H` all-pairs collision outcomes are not firmly established from accessible prose summaries alone. They should be treated as conjectural until direct local Rule 110 simulation verifies phase, spacing, transient cleanup, and outgoing products.

Before Phase B and C implementation can be trusted, the project still needs primary-diagram or simulation-derived templates for the leader package, each ossifier package, and the data-block encodings for logical `0` and `1`. The encoder design should therefore keep those structures behind named emitters and expose phase/separation metadata in collision tests rather than hard-coding a phase-free glider-pair table.
