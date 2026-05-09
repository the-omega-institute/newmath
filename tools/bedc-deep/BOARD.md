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

### B-570 - Polynomial multiplication has right zero absorption

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | Polynomial multiplication has right zero absorption |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 6/10 |

Problem:
For every CommRingUp scalar source R and finite coefficient spine p over R, the raw Cauchy product PolyMul_R(p, nil) is PolySame_R-classified with nil.

Local inputs:
- `papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex`

Rationale:
The chapter already proves the LEFT version `thm:polynomial-multiplication-left-zero-absorption` at 25_polynomial_literal_addtrim_algebra.tex:203, and proves multiplicative commutativity over commring scalars at 25_polynomial_literal_addtrim_algebra.tex:134 (`thm:polynomial-raw-multiplication-commutativity-from-commring-scalars`). Hence right-zero absorption follows by composing the two: PolyMul(p, nil) ~ PolyMul(nil, p) ~ nil. Standard textbook (Hungerford Algebra Ch.III §6, Lang Algebra Ch.IV §1: polynomial ring zero element is two-sided absorbing). No matching label in BOARD index. The file is 242 lines (well below the 760-line cap). Closes in 1 round: a 5-line proof citing two existing labels.

---


### B-571 - AffineSpace action by the zero vector classifies with the carried point

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | AffineSpace action by the zero vector classifies with the carried point |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If p is a carried point row in an AffineSpaceUp history-torsor carrier and 0_V is the vector zero supplied by its VecSpaceUp dependency certificate, then the action endpoint act(p, 0_V) and p are AffCls-classified by the identity case of the translation classifier.

Local inputs:
- `papers/bedc/parts/concrete_instances/184_affinespace_namecert_construction.tex`

Rationale:
The chapter proves the converse direction `thm:affinespace-separation-obligation` at 184_affinespace_namecert_construction.tex:84 ('if zero-translation acts sending p to ~q, then AffCls identifies p, q'), but the forward fact 'act(p, 0_V) ~ p' is not stated. Standard textbook (Berger Geometry I Ch.II §2.1, Audin Geometry §I.1: translation by 0 is the identity action). The proof reuses `thm:affinespace-action-closure-obligation` to carry the endpoint and `thm:affinespace-separation-obligation` to convert the zero-translation hsame witness into AffCls identity classification. File is 209 lines. Closes in 1-2 rounds; no oracle escalation needed because all infrastructure is already in this file.

---


### B-572 - ConvexSet pointwise (Minkowski) sum closes under the binary affine combination row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ConvexSet pointwise (Minkowski) sum closes under the binary affine combination row |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
If C and D are ConvexSetUp carriers over the same VecSpaceUp source V each supplying the binary affine-combination row, then the pointwise sum C+_*D := {z : ∃c,d, C(c) ∧ D(d) ∧ z ~_V c +_V d} also satisfies the binary affine-combination row of `def:convexset-binary-affine-combination-row`.

Local inputs:
- `papers/bedc/parts/concrete_instances/186_convexset_namecert_construction.tex`

Rationale:
The chapter has intersection (`thm:convexset-pointwise-intersection-affine-combination-closure` at 186_convexset_namecert_construction.tex:207), linear image (`thm:convexset-linear-image-affine-combination-closure`:250), and linear preimage (`thm:convexset-linear-preimage-affine-combination-closure`:369) closures, but NOT the Minkowski (pointwise) sum closure. Standard textbook (Rockafellar Convex Analysis Ch.II §3.1: 'if C, D are convex then C+D is convex'). Proof uses `def:convexset-binary-affine-combination-row` separately on C and D, then VecSpaceUp distributivity and middle-four interchange (`thm:abgroup-middle-four-interchange`) to regroup a(c1+d1) + b(c2+d2) as (ac1+bc2) + (ad1+bd2). All three pieces exist. File is 431 lines (room remains). Closes in 2-3 rounds. Not a parameter-transport echo: it constructs a new convex set from two and verifies the binary affine row, an explicit closure law.

---


### B-573 - InnerProduct norm-squared of scalar action factors as scalar self-product times norm-squared

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | InnerProduct norm-squared of scalar action factors as scalar self-product times norm-squared |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For every carried scalar r and carried vector x in an InnerProductUp BHist source, the norm-squared endpoint ||r ·_V x||²_I is classified by the retained scalar classifier with (r ·_K conj_K(r)) ·_K ||x||²_I.

Local inputs:
- `papers/bedc/parts/concrete_instances/innerproduct/norm_metric_seed.tex`

Rationale:
The chapter proves `thm:innerproduct-norm-squared-carrier-row` (carrier transport, 25_polynomial_literal_addtrim_eval would not be, this is innerproduct/norm_metric_seed.tex:25) and the linearity row `thm:innerproduct-vecspace-linearity-row` (innerproduct/core_surface.tex:121) handles both additive and scalar-action arguments with the conjugate handling promised on the conjugate-linear side. Polarization-difference and parallelogram are in the parallelogram seed. But the explicit norm-scaling identity ||r·x||²_I ~ (r·conj(r))·||x||²_I is missing — standard textbook (Folland Real Analysis Ch.5 §5.5, Conway Functional Analysis I §I.1.5: 'inner product is conjugate-bilinear, hence ||rx||² = |r|²||x||²'). Proof: apply linearity at left slot to extract r, then linearity at right slot with conjugation to extract conj(r), then scalar associativity. File norm_metric_seed.tex is only 101 lines. Closes in 2-3 rounds; the only nontrivial step is checking the conjugate-linearity clause of the existing linearity row at the right argument, which the row explicitly promises (core_surface.tex:140, 'the conjugate argument handled by the displayed conjugation row when the source uses that side as the conjugate-linear argument').

---

