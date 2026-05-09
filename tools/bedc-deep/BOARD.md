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

### B-581 - AdjointRepUp multiplicative homomorphism row Ad(gh) ~ Ad(g) o Ad(h)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AdjointRepUp multiplicative homomorphism row Ad(gh) ~ Ad(g) o Ad(h) |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
For carried Lie-group histories g,h and any carried algebra history t, Ad_{gh}(t) is classified by the LieAlgebraUp endomap classifier with the composite Ad_g(Ad_h(t)) without invoking a host group action.

Local inputs:
- `papers/bedc/parts/concrete_instances/121_adjointrep_namecert_construction.tex`

Rationale:
Fills the defining 'Ad is a representation' law inside 121_adjointrep. The chapter has conjugation-carrier, differential-action, automorphism-target, classifier-stability obligations but no homomorphism law on the action row itself. This is the canonical fact downstream representation-ring chapters cite, and is a trivial composite of LieGroupUp's multiplication ledger plus Ad's carrier-row construction.

---

### B-582 - RootSystemUp reflection involution s_alpha(s_alpha(beta)) ~ beta

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | RootSystemUp reflection involution s_alpha(s_alpha(beta)) ~ beta |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
For any carried root histories alpha and beta in a RootSystem BHist certificate, the displayed double reflection row s_alpha applied to s_alpha(beta) returns to a vector classified with beta under the InnerProductUp vector classifier, generated entirely from the displayed reflection Cont route and the Cartan integer endpoint.

Local inputs:
- `papers/bedc/parts/concrete_instances/122_rootsystem_namecert_construction.tex`

Rationale:
Distinct from B-454 (Weyl reflection words preserve roots) which is preservation under reflection words, not the order-2 involution row itself. 122_rootsystem has reflection-closure and Cartan-ledger but no theorem that s_alpha is involutive. Without it the WeylGroup bridge consumption theorem is incomplete — Weyl-group involutions are unwitnessed. Constructor inversion / determinism lemma at the most-cited level.

---

### B-583 - CliffordUp polarization identity uv + vu ~ q(u+v) - q(u) - q(v)

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | CliffordUp polarization identity uv + vu ~ q(u+v) - q(u) - q(v) |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 9/10 |

Problem:
For accepted vector histories u,v in the shared VecSpaceUp source, the Clifford classifier identifies u*v + v*u with q(u+v) - q(u) - q(v) via the displayed quadratic-relation row applied to u+v together with bilinearity transport from BilinFormUp.

Local inputs:
- `papers/bedc/parts/concrete_instances/125_clifford_namecert_construction.tex`

Rationale:
125_clifford has the diagonal quadratic-relation v*v ~ q(v)*1 and product-stability/confluence rows, but the universal symmetric polarization formula relating two distinct vectors is not derived. Polarization is the unique fact that distinguishes Clifford from a free tensor algebra and what downstream Spin/Pin certificates need to anchor double-cover constructions. Polarization shows up only in commring/innerproduct chapters elsewhere, never in Clifford. Frontier algebra capstone.

---

### B-584 - ModelTheoryUp elementary-equivalence reflexivity transport row

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | ModelTheoryUp elementary-equivalence reflexivity transport row |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For every admitted ModelTheoryUp source packet, Elem classifies the displayed structure A with itself under the trivial hsame transport, with reflexivity witnessed by the satisfaction-exactness row applied to identical formula and assignment endpoints, and no host model identity is invoked.

Local inputs:
- `papers/bedc/parts/concrete_instances/176_modeltheory_namecert_construction.tex`

Rationale:
176_modeltheory has elementary-transport (preservation under hsame) but no reflexivity row for Elem itself — the foundational equivalence-relation closure missing for the model classifier, analogous to saturated reflexivity rows already present for InnerProduct and ProbSpace. Every classifier needs reflexivity; the chapter is its own closure (438 lines, well under cap) and the proof is one application of satisfaction-exactness on identical endpoints.

---

### B-585 - AffineVarUp singleton-equation family zero-locus exactness

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (paper_review) |
| Object | AffineVarUp singleton-equation family zero-locus exactness |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
For any polynomial code p and the singleton finite-spine cons(p, nil), V_{R,n}(cons(p,nil))(x) holds iff AffPoint_{R,n}(x) and PolyEvalZero_{R,n}(p,x) both hold.

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`

Rationale:
132_affinevar has empty-family, concatenation, inclusion-reversal, duplicate-insertion, and mutual-inclusion rows but no canonical singleton (one-equation hypersurface) base case. This is the bridge case every downstream affine-variety consumer needs. Clean composite of empty-family-iff plus concatenation reading cons(p,nil) = cons(p, nil). Missing constructor case for the zero-locus carrier.

---

### B-586 - ClassFieldUp public interface theorem aggregating Artin / Frobenius / ledger obligations

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep topic discovery |
| Object | ClassFieldUp public interface theorem aggregating Artin / Frobenius / ledger obligations |
| Layer | adjacent |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 7/10 |

Problem:
If a package satisfies \autoref{thm:classfield-obligation-carrier-classifier}, \autoref{thm:classfield-obligation-artin-frobenius-stability}, and \autoref{thm:classfield-obligation-ledger-exactness}, then those three rows assemble into a single exported $\NameCert_{\ClassFieldUp}$ public interface certificate over the $\NumFieldUp$/$\AdeleUp$ source rows.

Local inputs:
- `papers/bedc/parts/concrete_instances/236_classfield_namecert_construction.tex`

Rationale:
papers/bedc/parts/concrete_instances/236_classfield_namecert_construction.tex declares upgradepath "Public closure requires a single exported $\ClassFieldUp$ public interface theorem or a checked bridge over the scoped certificate rows." File at 106 lines, with three obligation theorems clearly visible at lines 12, 24, 36 (verified by direct read). Notclaimed enumerates Artin reciprocity etc as out of scope, leaving only the aggregator. Grep `thm:classfield.*public` returns 0 hits. Single-implication aggregator over three explicitly-named obligation theorems — same B-565 pattern.

---
