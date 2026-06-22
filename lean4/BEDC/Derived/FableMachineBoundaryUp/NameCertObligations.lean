import BEDC.Derived.FableMachineBoundaryUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.FableMachineBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem FableMachineBoundaryNameCertObligations
    {history emptyBoundary ledger selector witness clock transport route provenance name boundaryRead :
      BHist} :
    Cont history emptyBoundary boundaryRead →
      UnaryHistory history →
        UnaryHistory emptyBoundary →
          UnaryHistory ledger →
            UnaryHistory selector →
              UnaryHistory witness →
                UnaryHistory clock →
                  UnaryHistory transport →
                    UnaryHistory route →
                      UnaryHistory provenance →
                        UnaryHistory name →
                          SemanticNameCert
                              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row history ∨ hsame row emptyBoundary ∨
                                  hsame row ledger ∨ hsame row selector ∨ hsame row witness ∨
                                    hsame row clock ∨ hsame row transport ∨
                                      hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                                        hsame row boundaryRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont history emptyBoundary boundaryRead)
                              hsame ∧
                            UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro boundaryRoute unaryHistory unaryEmptyBoundary unaryLedger unarySelector unaryWitness
    unaryClock unaryTransport unaryRoute unaryProvenance unaryName
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryHistory unaryEmptyBoundary boundaryRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left)))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, boundaryRoute⟩
    }
  · exact boundaryUnary

end BEDC.Derived.FableMachineBoundaryUp
