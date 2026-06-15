import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.FableMachineClockUp.TasteGate

namespace BEDC.Derived.FableMachineClockUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FableMachineClockStepLedgerExactness [AskSetup] [PackageSetup]
    {sourceHist stepLedger selectedMarks selectorWitnesses clockBoundary transport
      continuation provenance nameCert stepRead selectedRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory sourceHist →
      UnaryHistory stepLedger →
        UnaryHistory selectedMarks →
          UnaryHistory selectorWitnesses →
            UnaryHistory clockBoundary →
              Cont stepLedger selectedMarks stepRead →
                Cont stepRead selectorWitnesses selectedRead →
                  Cont selectedRead clockBoundary boundaryRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle nameCert pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row sourceHist ∨ hsame row stepLedger ∨
                                hsame row selectedMarks ∨ hsame row selectorWitnesses ∨
                                  hsame row clockBoundary ∨ hsame row boundaryRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧
                                Cont stepLedger selectedMarks stepRead ∧
                                  Cont stepRead selectorWitnesses selectedRead ∧
                                    Cont selectedRead clockBoundary boundaryRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle nameCert pkg)
                            hsame ∧
                          UnaryHistory stepRead ∧ UnaryHistory selectedRead ∧
                            UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro _sourceUnary stepUnary selectedUnary selectorUnary boundaryUnary stepRoute
    selectedRoute boundaryRoute provenancePkg nameCertPkg
  have stepReadUnary : UnaryHistory stepRead :=
    unary_cont_closed stepUnary selectedUnary stepRoute
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed stepReadUnary selectorUnary selectedRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed selectedReadUnary boundaryUnary boundaryRoute
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceHist ∨ hsame row stepLedger ∨ hsame row selectedMarks ∨
              hsame row selectorWitnesses ∨ hsame row clockBoundary ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stepLedger selectedMarks stepRead ∧
              Cont stepRead selectorWitnesses selectedRead ∧
                Cont selectedRead clockBoundary boundaryRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, stepRoute, selectedRoute, boundaryRoute, provenancePkg,
            nameCertPkg⟩
    }
  exact ⟨cert, stepReadUnary, selectedReadUnary, boundaryReadUnary⟩

end BEDC.Derived.FableMachineClockUp
