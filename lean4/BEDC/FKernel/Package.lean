import BEDC.FKernel.Sig

/-! Packages expose visible tokens for internally generated signatures. -/
namespace BEDC.FKernel.Package

open BEDC.FKernel.Hist


axiom Pi : Type
axiom Pkg : Type
axiom TokIntro : Pi → BHist → Pkg → Prop
axiom psame : Pkg → Pkg → Prop

structure PackagePolicy (P : Pi) : Prop where
  existence : ∀ s : BHist, ∃ p : Pkg, TokIntro P s p
  extensionality :
    ∀ {s t : BHist} {p q : Pkg}, hsame s t → TokIntro P s p → TokIntro P t q → psame p q
  grounding :
    ∀ {p q : Pkg}, psame p q → ∃ s : BHist, ∃ t : BHist, TokIntro P s p ∧ TokIntro P t q ∧ hsame s t

end BEDC.FKernel.Package
