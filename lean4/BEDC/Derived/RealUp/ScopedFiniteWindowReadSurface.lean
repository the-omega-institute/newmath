import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealupScopedFiniteWindowReadSurface
    {dyadic regseq stream rat endpoint ledger : BHist} :
    UnaryHistory dyadic ->
    UnaryHistory regseq ->
    UnaryHistory rat ->
    Cont dyadic regseq stream ->
    Cont stream rat endpoint ->
    Cont endpoint stream ledger ->
    UnaryHistory stream ∧ UnaryHistory endpoint ∧ UnaryHistory ledger ∧
      hsame stream (append dyadic regseq) ∧ hsame endpoint (append stream rat) ∧
        hsame ledger (append endpoint stream) := by
  intro dyadicUnary regseqUnary ratUnary streamCont endpointCont ledgerCont
  have streamUnary : UnaryHistory stream :=
    unary_cont_closed dyadicUnary regseqUnary streamCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed streamUnary ratUnary endpointCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpointUnary streamUnary ledgerCont
  exact And.intro streamUnary
    (And.intro endpointUnary
      (And.intro ledgerUnary
        (And.intro streamCont (And.intro endpointCont ledgerCont))))

end BEDC.Derived.RealUp
