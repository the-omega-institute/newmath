import BEDC.FKernel.Sig

/-! Packages expose visible tokens for internally generated signatures. -/
namespace BEDC.FKernel.Package

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

class PackageSetup [AskSetup] where
  Pkg : Type
  TokIntro : ProbeBundle ProbeName → BHist → Pkg → Prop

variable [AskSetup] [P : PackageSetup]

abbrev Pkg : Type := P.Pkg
abbrev TokIntro : ProbeBundle ProbeName → BHist → Pkg → Prop := P.TokIntro

inductive psame (bundle : ProbeBundle ProbeName) : Pkg → Pkg → Prop where
  | intro {s t : BHist} {p q : Pkg} :
      TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q

theorem psame_sound {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q := by
  intro hp hq hst
  exact psame.intro hp hq hst

structure PackagePolicy (bundle : ProbeBundle ProbeName) : Prop where
  existence : ∀ s : BHist, ∃ p : Pkg, TokIntro bundle s p
  extensionality :
    ∀ {s t : BHist} {p q : Pkg}, hsame s t → TokIntro bundle s p → TokIntro bundle t q → psame bundle p q
  grounding :
    ∀ {p q : Pkg}, psame bundle p q → ∃ s : BHist, ∃ t : BHist, TokIntro bundle s p ∧ TokIntro bundle t q ∧ hsame s t

theorem packagePolicy_classifies_signatures
    {bundle : ProbeBundle ProbeName} (policy : PackagePolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (psame bundle p q →
        ∃ u : BHist, ∃ v : BHist,
          TokIntro bundle u p ∧ TokIntro bundle v q ∧ hsame u v) ∧
      (hsame s t → psame bundle p q) := by
  intro left right
  constructor
  · intro samePkg
    exact policy.grounding samePkg
  · intro sameHist
    exact policy.extensionality sameHist left right

structure PackageTokenPolicy (bundle : ProbeBundle ProbeName) : Prop where
  soundness :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q
  reflection :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t

theorem psame_reflect {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> hsame s t := by
  intro policy hp hq hpq
  exact policy.reflection hp hq hpq

theorem package_reflection {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle -> TokIntro bundle s p -> TokIntro bundle t q -> psame bundle p q -> hsame s t := by
  intro policy hp hq hpq
  exact policy.reflection hp hq hpq

theorem packageTokenPolicy_from_reflection
    {bundle : ProbeBundle ProbeName}
    (reflection :
      ∀ {s t : BHist} {p q : Pkg},
        TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t) :
    PackageTokenPolicy bundle := by
  exact {
    soundness := by
      intro s t p q hp hq hst
      exact psame.intro hp hq hst
    reflection := by
      intro s t p q hp hq hpq
      exact reflection hp hq hpq
  }

theorem concrete_package_token_policy
    {bundle : ProbeBundle ProbeName}
    (reflection :
      ∀ {s t : BHist} {p q : Pkg},
        TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t) :
    PackageTokenPolicy bundle := by
  exact packageTokenPolicy_from_reflection reflection

theorem psame_iff_hsame
    {bundle : ProbeBundle ProbeName} {s t : BHist} {p q : Pkg} :
    PackageTokenPolicy bundle →
      TokIntro bundle s p → TokIntro bundle t q → (psame bundle p q ↔ hsame s t) := by
  intro policy left right
  constructor
  · intro samePkg
    exact policy.reflection left right samePkg
  · intro sameHist
    exact policy.soundness left right sameHist

def MinimalPackageSetup [AskSetup] : PackageSetup where
  Pkg := Unit
  TokIntro := fun _ _ _ => True

end BEDC.FKernel.Package
