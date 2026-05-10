# BEDC Deep Reasoning Board

Purpose: drive a self-iterating BEDC paper-extension loop. Each entry below is
a target the oracle deep-reasoning loop runs to a complete result, then
appends as canonical current-state LaTeX into `papers/bedc/parts/`. The
downstream `lean4/scripts/codex_formalize.py` lane (on dev) picks up new
theorem sites by scanning the paper.

Lane edge:
- This lane never edits `lean4/`. The handshake to formalization is the
  appended LaTeX in `papers/bedc/parts/<theme>/<concept>.tex` (no marker
  macros — those are added by `codex_formalize.py` after the Lean target lands).
- New targets are auto-spawned by Stage 1.5 topic discovery and appended to
  this board with `Status: Candidate (auto-spawned)`.

Each target card carries enough context (Object, Local inputs) for the loop
to build its initial prompt without external lookups.

---

### B-617 - Module LinearMap pointwise sum associativity

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Module LinearMap pointwise sum associativity |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If LinearMapCert_R(M,N;f), LinearMapCert_R(M,N;g), and LinearMapCert_R(M,N;h) all hold over common ModuleUp(R,M),ModuleUp(R,N) certificates, then the pointwise sums (f+g)+h and f+(g+h) carry LinearMapUp(M,N) certificates and are pointwise-classifier-equal.

Local inputs:
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_kernel_image_and_zero.tex`
- `papers/bedc/parts/concrete_instances/linearmap/module_linearmap_certificates.tex`

Rationale:
The commutativity counterpart is at module_linearmap_kernel_image_and_zero.tex:101 (thm:module-linearmap-pointwise-sum-commutativity) and the binary pointwise-sum certificate is at module_linearmap_certificates.tex:344 (thm:module-linearmap-pointwise-sum-certificate). Composition associativity exists at module_linearmap_certificates.tex:238, but pointwise *sum* associativity does not: grep 'pointwise-sum-assoc\|pointwise.*sum.*associat' across papers/ returns only composition-assoc and FPS pointwise-additive-group-laws references. Build from two applications of pointwise-sum-certificate plus the target module's additive associativity (via prop:module-forgets-abgroup-certificate). Landing file 182 lines, ample room. Concrete classifier comparison, not parameter echo.

---


### B-618 - GaloisGroupUp inverse-of-composition antimultiplicative row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | GaloisGroupUp inverse-of-composition antimultiplicative row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For accepted automorphism-action rows x and y in a GaloisGroupUp packet, the inverse of the composed row x \circ y is classifier-equal to y^{-1} \circ x^{-1} via the public GaloisExtUp endpoint classifier and the inherited GroupUp surface.

Local inputs:
- `papers/bedc/parts/concrete_instances/galoisgroup/composition_and_inverse_laws.tex`
- `papers/bedc/parts/concrete_instances/galoisgroup/group_law_package.tex`

Rationale:
composition_and_inverse_laws.tex contains thm:galoisgroup-composition-associativity-row (line 2), thm:galoisgroup-inverse-cancellation-rows (line 43), and thm:galoisgroup-inverse-involution-row (line 187), plus thm:galoisgroup-composition-classifier-congruence (line 116). The antimultiplicative inverse rule (g h)^{-1} ~ h^{-1} g^{-1}, the natural completion of the composition+inverse algebra, is missing: grep 'inverse-of-composition\|composition-inverse\|inverse-product' across the galoisgroup/ subdirectory returns no hits. Built from inverse-closure (carrier_and_basic_laws.tex:146) plus the GroupUp dependency's inverse-of-product law (referenced as thm:group-inverse-mul-reverse, used in spingroup/boundary_consumer_exactness.tex:127). File 235 lines, ample room. Concrete inversion identity, not transport.

---


### B-619 - Independence two-element index family carries the finite factorisation row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Independence two-element index family carries the finite factorisation row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If a finite-family IndependenceUp carrier has exactly two certified positions i_0, i_1, with the displayed product-cylinder ledger reducing the joint endpoint to mu_{i_0}(B_{i_0}) \cdot_R mu_{i_1}(B_{i_1}) and the two-element RealUp product fold evaluating to the same product, then for every measurable two-position event family B the displayed data carry the finite factorisation row of def:independence-finite-factorisation-row.

Local inputs:
- `papers/bedc/parts/concrete_instances/165_independence_namecert_construction.tex`

Rationale:
165_independence_namecert_construction.tex:367 proves thm:independence-empty-index-factorization-row (B-527 / B-587 area); line 416 proves thm:independence-singleton-index-factorization-row (B-591 in board). The two-element case is the *first* arity where a real product fold actually multiplies two distinct factors, and is genuinely missing: grep 'two-element\|binary.factorisation\|pair.factorisation\|two.position' across papers/ shows no Independence two-element row. Builds on the pushforward rows already used in the singleton proof plus the binary RealUp product fold (used elsewhere in concrete_instances/). File 471 lines, room available. Concrete arity step: requires a real factorisation calculation, not just a transport.

---


### B-620 - SpinGroup conjugation action inverse-involution row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | SpinGroup conjugation action inverse-involution row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 6/10 |

Problem:
For an accepted SpinGroupUp packet S with visible Clifford-unit endpoint s and any accepted Clifford-vector row v, the iterated action endpoint Act_{s^{-1}}(Act_s(v)) is an accepted Clifford-vector row in the same packet and is classifier-equal to v under the generated CliffordUp classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/spingroup/boundary_consumer_exactness.tex`

Rationale:
spingroup/boundary_consumer_exactness.tex:78 proves thm:spingroup-conjugation-action-product-law (B-600 in board) and line 160 proves thm:spingroup-conjugation-action-identity-law (B-612). The natural composition s^{-1}\cdot s = e route — Act_{s^{-1}}(Act_s(v)) ~ Act_e(v) ~ v — is not stated as its own theorem: grep 'spingroup.*inverse.action\|conjugation.action.inverse\|conjugation.*inverse.law' across papers/ returns nothing. The proof composes product-law (with t=s^{-1}) and identity-law plus the GroupUp inverse field already named in carrier_and_basic_laws.tex pattern. Concrete inversion-cancellation identity over the displayed Clifford ledger, not transport. File 231 lines, ample room.

---

