import BEDC.Derived.RealityConstrainedPhysicalInductionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedPhysicalInductionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RealityConstrainedPhysicalInductionNameCertObligations
    {H U T S O A C B F L K P N endpoint : BHist} :
    RealityConstrainedPhysicalInductionUp →
      UnaryHistory endpoint →
        Cont H U C →
          Cont C B F →
            Cont F L endpoint →
              SemanticNameCert
                (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                (fun row : BHist => hsame row endpoint ∧ Cont H U C ∧ Cont C B F)
                (fun row : BHist => hsame row endpoint ∧ Cont F L endpoint)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier endpointUnary huc cbf fle
  cases carrier with
  | mk _H _U _T _S _O _A _C _B _F _L _K _P _N =>
      exact {
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
          exact ⟨source.left, huc, cbf⟩
        ledger_sound := by
          intro _row source
          exact ⟨source.left, fle⟩
      }

theorem RealityConstrainedPhysicalInductionCarrier_continuation_scope
    {H U T S O A C B F L K P N endpoint predicted : BHist} :
    UnaryHistory H →
      UnaryHistory U →
        UnaryHistory B →
          UnaryHistory L →
            UnaryHistory K →
              Cont H U C →
                Cont C B F →
                  Cont F L endpoint →
                    Cont endpoint K predicted →
                      ∃ carrier : RealityConstrainedPhysicalInductionUp,
                        carrier =
                            RealityConstrainedPhysicalInductionUp.mk H U T S O A C B F L K P N ∧
                          UnaryHistory C ∧
                            UnaryHistory F ∧
                              UnaryHistory endpoint ∧
                                UnaryHistory predicted ∧
                                  Cont H U C ∧
                                    Cont C B F ∧
                                      Cont F L endpoint ∧ Cont endpoint K predicted := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro historyUnary finiteFitUnary stabilityUnary ledgerUnary transportUnary historyFitRoute
    continuationFailureRoute failureLedgerRoute endpointPredictionRoute
  have continuationUnary : UnaryHistory C :=
    unary_cont_closed historyUnary finiteFitUnary historyFitRoute
  have failureUnary : UnaryHistory F :=
    unary_cont_closed continuationUnary stabilityUnary continuationFailureRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed failureUnary ledgerUnary failureLedgerRoute
  have predictedUnary : UnaryHistory predicted :=
    unary_cont_closed endpointUnary transportUnary endpointPredictionRoute
  exact
    ⟨RealityConstrainedPhysicalInductionUp.mk H U T S O A C B F L K P N, rfl,
      continuationUnary, failureUnary, endpointUnary, predictedUnary, historyFitRoute,
      continuationFailureRoute, failureLedgerRoute, endpointPredictionRoute⟩

end BEDC.Derived.RealityConstrainedPhysicalInductionUp
