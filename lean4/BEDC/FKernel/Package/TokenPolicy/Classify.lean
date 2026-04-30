import BEDC.FKernel.Package.TokenPolicy

namespace BEDC.FKernel.Package

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle

theorem packageTokenPolicy_psame_hsame_equivalence_fields [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (psame bundle p q → hsame s t) ∧ (hsame s t → psame bundle p q) := by
  intro left right
  constructor
  · intro samePkg
    exact policy.reflection left right samePkg
  · intro sameHist
    exact policy.soundness left right sameHist

theorem package_reflection_roundtrip_pair [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (psame bundle p q → hsame s t) ∧ (hsame s t → psame bundle p q) := by
  intro left right
  constructor
  · intro samePkg
    exact policy.reflection left right samePkg
  · intro sameHist
    exact policy.soundness left right sameHist

theorem packageTokenPolicy_classification_iff_symm_on_introduced [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p -> TokIntro bundle t q -> (psame bundle q p <-> hsame t s) := by
  intro left right
  exact packageTokenPolicy_compares_introduced_by_psame policy right left

theorem packageTokenPolicy_classification_roundtrip_on_introduced [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} (policy : PackageTokenPolicy bundle)
    {s t : BHist} {p q : Pkg} :
    TokIntro bundle s p → TokIntro bundle t q →
      (hsame s t → psame bundle p q) ∧ (psame bundle p q → hsame s t) := by
  intro left right
  constructor
  · intro sameHist
    exact policy.soundness left right sameHist
  · intro samePkg
    exact policy.reflection left right samePkg

end BEDC.FKernel.Package
