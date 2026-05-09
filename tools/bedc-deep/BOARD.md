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

### B-564 - AxisAdd zero-spine result inversion: prefix and suffix inherit zero-spine

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AxisAdd zero-spine result inversion: prefix and suffix inherit zero-spine |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If ContR(h, k, r) and ZeroSpine(r) hold, then both ZeroSpine(h) and ZeroSpine(k) hold.

Local inputs:
- `papers/bedc/parts/concrete_instances/255_axisadd_namecert_construction.tex`

Rationale:
Converse of `thm:axisadd-cont-preserves-zerospine` (line 86). Forward direction is ZS(h)∧ZS(k)∧Cont(h,k,r) → ZS(r); the inversion ZS(r)∧Cont(h,k,r) → ZS(h)∧ZS(k) is missing. Constructor-inversion / no-confusion lemma against the Ezero generator. Closes the source/result classification round-trip on AxisAddUp without invoking AddUp bridge. Distinct from B-553 (which lives in axisnat and concerns source shape exhaustion). Lands in 255_axisadd_namecert_construction.tex (134 lines).

---


### B-565 - UnitaryGroupUp public certificate theorem aggregating its four obligation rows

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | UnitaryGroupUp public certificate theorem aggregating its four obligation rows |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
The carrier-classifier, operation-stability, inner-product-preservation, and ledger-exactness obligations together exhibit a public NameCert_{UnitaryGroupUp} export over the HilbertUp and LieGroupUp sources.

Local inputs:
- `papers/bedc/parts/concrete_instances/197_unitarygroup_namecert_construction.tex`

Rationale:
Chapter sits at scopedClosure with explicit upgradepath demanding exactly this aggregator. The four obligation theorems are present in the file but never composed into the public NameCert export. Standard BEDC public-closure pattern (matches `spectraltheorem-public-certificate` shape). Lands cleanly in 197_unitarygroup_namecert_construction.tex (114 lines, ample room).

---


### B-566 - DiffForm exterior-derivative two-step composability ledger

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | DiffForm exterior-derivative two-step composability ledger |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If two accepted DiffForm exterior-derivative input rows over (omega,eta) and (eta,theta) share the middle eta, the composite exposes the two-step degree continuation row ContR(d_omega, E1(E1(emp)), d_theta).

Local inputs:
- `papers/bedc/parts/concrete_instances/114_diffform_exterior_derivative_boundary.tex`

Rationale:
Chapter currently carries only one-step degree-shift boundary (line 106) and explicitly defers d²=0 to DeRham. B-543 is the DeRham-side nilpotence; the DiffForm-side composability ledger (without d²=0 assertion) is the missing precursor that the DeRham proof would consume. Two-step continuation row is a classic composite consequence with clear binder shape. Lands in 114_diffform_exterior_derivative_boundary.tex (158 lines).

---


### B-567 - Hash second-preimage success is irreflexive on the message

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | Hash second-preimage success is irreflexive on the message |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
Under message-classifier reflexivity, HashSecondPreimageSuccess_{mathcal H}(x, x) is impossible: no transcript can witness a second-preimage with itself.

Local inputs:
- `papers/bedc/parts/concrete_instances/220_hash_namecert_construction.tex`

Rationale:
Direct analogue of B-523 (collision irreflexivity at line 293-326) for second-preimage success. The transcript predicate requires neg sigma(x,x') as part of definition, so reflexivity of sigma forces irreflexivity. Distinct from B-489 (collision-freeness excludes second-preimage — that's the resistance direction, not the diagonal-impossibility direction). The dual is mentioned nowhere in the existing 220_hash file. Sits comfortably alongside the existing irreflexivity / induces-direction / boundary theorems. 413 lines, well below cap.

---

### B-568 - Banach identity bounded-linear operator carrier construction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Banach identity bounded-linear operator carrier construction |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
If C is a BanachUp candidate, then BanachBLOp(C, C, id_C, 1_RealUp, I_C) is carried, where id_C is the source identity map and I_C records the reflexivity, multiplicative-unit, RealUp non-negativity, and norm rows used by the carrier definition.

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex`

Rationale:
The Banach bounded-operator carrier is defined at papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex:1-31 with four carrier rows (classifier-respect, additivity, scalar action, RealUp bound). The zero operator carrier is constructed as a theorem at the same file, line 145 (B-480 on the BOARD). The IDENTITY operator carrier, by contrast, is only referenced as a hypothesis at bounded_linear_operator_composition.tex:319 ('Assume also that the source and target identity maps carry the unit bound: BanachBLOp(C,C,id_C,1_RealUp,I_C)'); no theorem CONSTRUCTS this carrier from the BanachUp axioms. A grep for `Banach.*identity.*operator.*carrier` returns no theorem-environment match across papers/bedc/parts/, and no Lean target named BanachIdentityBoundedLinearOperator_carrier or similar exists under lean4/BEDC/. The construction is a concrete one-shot proof using Banach C's classifier reflexivity, the RealUp multiplicative-identity row 1·r ~ r, and 1 ≥ 0; it parallels the zero-operator carrier proof at bounded_linear_operator_obligations.tex:163-194 in shape but uses different scalar-row witnesses, so it is not a parameter echo. Filling this gap also discharges the unit-ledger hypothesis hand-waved at line 319 of the composition file.

---


### B-569 - Banach bounded operator zero right-composition annihilation

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Banach bounded operator zero right-composition annihilation |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
If T : H_0 -> H_1 is a carried BanachBLOp row and 0_{H_1,H_2} : H_1 -> H_2 is the carried zero operator on (H_1, H_2), then 0_{H_1,H_2} ∘ T is carried as BanachBLOp(H_0, H_2, 0_{H_1,H_2} ∘ T, 0_RealUp · L, Lambda_{12} ⋆ Gamma) and is classified with the zero representative on (H_0, H_2).

Local inputs:
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex`
- `papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_obligations.tex`

Rationale:
papers/bedc/parts/concrete_instances/banach/bounded_linear_operator_composition.tex:368 carries `thm:banach-bounded-linear-operator-left-zero-annihilation` (BOARD B-522), which composes T : H_1 -> H_2 with the input-side zero 0_{H_0,H_1} to get the (H_0,H_2) zero. The DUAL — composing T : H_0 -> H_1 with the output-side zero 0_{H_1,H_2} — is structurally absent. A grep for `[Bb]anach.*[Rr]ight.*[Zz]ero.*[Aa]nnihilat`, `right-composition`, and `Banach.*right.*zero` across papers/bedc/parts/ returns zero theorem matches; the only hit is the in-proof phrase 'right-zero multiplication comparison' at line 443 of the same file, used as a RealUp identity, not as a separate theorem. By contrast, papers/bedc/parts/concrete_instances/154_abeliancat_namecert_construction.tex:435 carries `thm:abeliancat-zero-morphism-right-composition-absorption` and BOARD entries B-518 (left-absorbing) and B-531 (right-absorbing) appear as a paired set for AbelianCat — the asymmetry on the Banach side is therefore a real gap, not a deliberate scope cut. The proof structurally differs from B-522: zero ∘ T evaluates to 0 by the output-zero map's defining row, not via T's homogeneity, so it is not just symmetry on existing arguments.

---

