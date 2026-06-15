import BEDC.Derived.CauchyRootCriterionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRootCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyRootCriterionNamecertObligations [AskSetup] [PackageSetup]
    {series rootBound window tolerance handoff readback sealRow _transport replay provenance
      _localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory series →
      UnaryHistory rootBound →
        UnaryHistory tolerance →
          UnaryHistory readback →
            UnaryHistory sealRow →
              Cont series rootBound window →
                Cont window tolerance handoff →
                  Cont handoff readback replay →
                    Cont replay sealRow endpoint →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle endpoint pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row series ∨ hsame row rootBound ∨
                                  hsame row window ∨ hsame row tolerance ∨
                                    hsame row handoff ∨ hsame row readback ∨
                                      hsame row sealRow ∨ hsame row endpoint)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle provenance pkg)
                              hsame ∧ UnaryHistory window ∧ UnaryHistory handoff ∧
                            UnaryHistory replay ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame SemanticNameCert
  intro seriesUnary rootBoundUnary toleranceUnary readbackUnary sealUnary
  intro windowRoute handoffRoute replayRoute endpointRoute provenancePkg endpointPkg
  have windowUnary : UnaryHistory window :=
    unary_cont_closed seriesUnary rootBoundUnary windowRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed windowUnary toleranceUnary handoffRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed handoffUnary readbackUnary replayRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary sealUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row series ∨ hsame row rootBound ∨ hsame row window ∨
            hsame row tolerance ∨ hsame row handoff ∨ hsame row readback ∨
                hsame row sealRow ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg, provenancePkg⟩
  }
  exact ⟨cert, windowUnary, handoffUnary, replayUnary, endpointUnary⟩

end BEDC.Derived.CauchyRootCriterionUp
