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

structure PackageTokenPolicy (bundle : ProbeBundle ProbeName) : Prop where
  soundness :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → hsame s t → psame bundle p q
  reflection :
    ∀ {s t : BHist} {p q : Pkg}, TokIntro bundle s p → TokIntro bundle t q → psame bundle p q → hsame s t

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
