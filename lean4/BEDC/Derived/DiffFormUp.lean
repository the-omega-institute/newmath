import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DiffFormBHistCarrier_coordinate_ledger
    {degree probe tensor scalar antisym ledger : BHist}
    (degreeUnary : UnaryHistory degree) (probeUnary : UnaryHistory probe)
    (tensorRoute : Cont degree probe tensor)
    (antisymUnary : UnaryHistory antisym)
    (scalarRoute : Cont tensor antisym scalar)
    (ledgerRoute : hsame ledger (append degree (append probe (append tensor (append scalar antisym))))) :
    UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧ UnaryHistory scalar ∧
      hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) := by
  have tensorUnary : UnaryHistory tensor := by
    cases tensorRoute
    exact unary_append_closed degreeUnary probeUnary
  have scalarUnary : UnaryHistory scalar := by
    cases scalarRoute
    exact unary_append_closed tensorUnary antisymUnary
  exact ⟨degreeUnary, probeUnary, tensorUnary, scalarUnary, ledgerRoute⟩

end BEDC.Derived.DiffFormUp
