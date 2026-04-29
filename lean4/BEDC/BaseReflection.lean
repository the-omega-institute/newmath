/-!
BEDC base-reflection scaffold.

This file is independent illustrative scaffolding for the paper-side
base-reflection contract. It does not share types with the `BEDC.FKernel.*`
modules and should be read as a separate abstract interface.

Phase 1 acceptance: this file compiles in Lean 4 v4.28.0 (mathlib-free).

The source manuscript at .source/lean/BEDC_v1_5_5_BaseReflection_Scaffold.lean
self-described as "theorem-shape documentation, not a verified release artifact"
and contains structural mismatches with strict Lean 4 type theory:

  * `PBaseData` and `GeneratedSameSig` originally declared `: Prop` but carry
    `SigObj`/`Evidence` (`Type`) fields. Lean 4 forbids such fields in a Prop
    structure (proof irrelevance breaks). They are made `: Type` here.
  * `PsameBase_inversion : PsameBase ... → PBaseData ...` would need large
    elimination from a non-singleton Prop, which is unsound. Wrapped in
    `Nonempty` to stay in Prop and stubbed `sorry`.
  * Universe polymorphism (`Type u`) caused universe-mismatch errors inside
    `ExactGlobalizeBase_classify_iff`. Pinned to `Type 0`.

v0.2 will redesign these structures. For v0.1 the goal is `lake build` exit 0
with sorry-d allowed.
-/

namespace BEDC.BaseReflection

axiom Hist : Type
axiom SigObj : Type
axiom Pkg : Type
axiom Pi : Type
axiom Domain : Type
axiom Evidence : Type

axiom hsame : SigObj → SigObj → Prop

structure HSameEquiv : Prop where
  refl  : ∀ s, hsame s s
  symm  : ∀ {s t}, hsame s t → hsame t s
  trans : ∀ {r s t}, hsame r s → hsame s t → hsame r t

axiom InDom : Domain → Hist → Prop
axiom SigGen : Pi → Hist → SigObj → Evidence → Prop
axiom TokIntro : Pi → SigObj → Pkg → Prop
axiom InGapSig : Pi → Domain → Pkg → Hist → Prop

structure TokUnique (P : Pi) : Prop where
  tokenReplacement : ∀ {s t p},
    TokIntro P s p → TokIntro P t p → hsame s t

inductive PsameBase (P : Pi) : Pkg → Pkg → Prop where
  | intro {s t : SigObj} {p q : Pkg} :
      TokIntro P s p → TokIntro P t q → hsame s t → PsameBase P p q

/-- Data record extracted from a `PsameBase` proof. Source had this as `Prop`
with `Type` fields, which Lean 4 rejects; lifted to `Type`. -/
structure PBaseData (P : Pi) (p q : Pkg) : Type where
  s : SigObj
  t : SigObj
  leftIntro : TokIntro P s p
  rightIntro : TokIntro P t q
  sigSame : hsame s t

/-- Stubbed at v0.1: extracting `Type` data from a `Prop` requires large
    elimination of `PsameBase`, which is non-singleton (different `(s,t)`
    inhabit different inductive constructors). Will be redesigned in v0.2. -/
theorem PsameBase_inversion {P : Pi} {p q : Pkg} :
    PsameBase P p q → Nonempty (PBaseData P p q) := by
  sorry

theorem PackageReflection_base
    {P : Pi} (eqv : HSameEquiv) (tok : TokUnique P)
    {s t : SigObj} {p q : Pkg}
    (left : TokIntro P s p) (right : TokIntro P t q)
    (base : PsameBase P p q) : hsame s t := by
  cases base with
  | intro left0 right0 same0 =>
      have s_to_s0 := tok.tokenReplacement left left0
      have t_to_t0 := tok.tokenReplacement right right0
      exact eqv.trans (eqv.trans s_to_s0 same0) (eqv.symm t_to_t0)

/-- Same structural reason as `PBaseData`: source had `: Prop` with `Type` fields. -/
structure GeneratedSameSig (P : Pi) (h k : Hist) : Type where
  s : SigObj
  t : SigObj
  de : Evidence
  th : Evidence
  leftSig : SigGen P h s de
  rightSig : SigGen P k t th
  sigSame : hsame s t

/-- `completeness` wraps `GeneratedSameSig` (a `Type`) in `Nonempty` so the
    structure stays in `Prop`. Phrasing-equivalent to the source intent. -/
structure ExactGlobalizeBase (P : Pi) (D : Domain) : Prop where
  coverage : ∀ h, InDom D h → ∃ p, InGapSig P D p h
  soundness : ∀ h k p q,
    InGapSig P D p h → InGapSig P D q k →
    GeneratedSameSig P h k → PsameBase P p q
  completeness : ∀ h k p q,
    InGapSig P D p h → InGapSig P D q k →
    PsameBase P p q → Nonempty (GeneratedSameSig P h k)

/-- Stubbed at v0.1: depends on `PBaseData` Prop/Type tension above. v0.2 fix. -/
theorem ExactGlobalizeBase_classify_iff
    {P : Pi} {D : Domain} (ex : ExactGlobalizeBase P D)
    {h k : Hist} {p q : Pkg}
    (hp : InGapSig P D p h) (hq : InGapSig P D q k) :
    PsameBase P p q ↔ Nonempty (GeneratedSameSig P h k) := by
  sorry

end BEDC.BaseReflection
