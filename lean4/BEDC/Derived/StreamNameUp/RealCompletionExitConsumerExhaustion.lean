import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem StreamNameRealCompletionFourObjectExitConsumerExhaustion
    {window ledger readback sealRow exitRead : BHist} :
    UnaryHistory window ->
      UnaryHistory ledger ->
        UnaryHistory readback ->
          UnaryHistory sealRow ->
            Cont window ledger readback ->
              Cont readback sealRow exitRead ->
                UnaryHistory window ∧ UnaryHistory ledger ∧ UnaryHistory readback ∧
                  UnaryHistory sealRow ∧ UnaryHistory exitRead ∧
                    Cont window ledger readback ∧ Cont readback sealRow exitRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro windowUnary ledgerUnary readbackUnary sealUnary windowLedgerRoute exitRoute
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed readbackUnary sealUnary exitRoute
  exact
    ⟨windowUnary, ledgerUnary, readbackUnary, sealUnary, exitUnary, windowLedgerRoute,
      exitRoute⟩

end BEDC.Derived.StreamNameUp
