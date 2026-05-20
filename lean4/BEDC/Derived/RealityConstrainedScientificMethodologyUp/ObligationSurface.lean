import BEDC.Derived.RealityConstrainedScientificMethodologyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedScientificMethodologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedScientificMethodology_obligation_surface [AskSetup] [PackageSetup]
    {X A E I D L F R T C P N explanationRoute idealizationRoute leakageRoute
      namedMethodology : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X E explanationRoute →
      Cont I D idealizationRoute →
        Cont D L leakageRoute →
          Cont leakageRoute N namedMethodology →
            PkgSig bundle namedMethodology pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row namedMethodology)
                  (fun row : BHist =>
                    hsame row explanationRoute ∨ hsame row idealizationRoute ∨
                      hsame row leakageRoute ∨ hsame row namedMethodology)
                  (fun row : BHist =>
                    PkgSig bundle namedMethodology pkg ∧ hsame row namedMethodology)
                  hsame ∧
                TasteGate.realityConstrainedScientificMethodologyFields
                    (TasteGate.RealityConstrainedScientificMethodologyUp.mk X A E I D L F R T C
                      P N) =
                  [X, A, E, I, D, L, F, R, T, C, P, N] ∧
                  Cont X E explanationRoute ∧
                    Cont I D idealizationRoute ∧
                      Cont D L leakageRoute ∧ Cont leakageRoute N namedMethodology := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro explanationCont idealizationCont leakageCont namedCont namedPkg
  have sourceNamed :
      (fun row : BHist => hsame row namedMethodology) namedMethodology := by
    exact hsame_refl namedMethodology
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedMethodology)
          (fun row : BHist =>
            hsame row explanationRoute ∨ hsame row idealizationRoute ∨
              hsame row leakageRoute ∨ hsame row namedMethodology)
          (fun row : BHist => PkgSig bundle namedMethodology pkg ∧ hsame row namedMethodology)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedMethodology sourceNamed
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source))
    ledger_sound := by
      intro _row source
      exact ⟨namedPkg, source⟩
  }
  exact
    ⟨cert, rfl, explanationCont, idealizationCont, leakageCont, namedCont⟩

end BEDC.Derived.RealityConstrainedScientificMethodologyUp
