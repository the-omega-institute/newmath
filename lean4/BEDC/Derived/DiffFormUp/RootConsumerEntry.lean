import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormRootConsumerEntry_carrier {degree probe tensor scalar antisym ledger target : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont ledger BHist.Empty target ->
            UnaryHistory target ∧ hsame target ledger ∧ UnaryHistory tensor ∧
              UnaryHistory scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute targetRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport
      (unary_append_closed coordinateRows.left
        (unary_append_closed coordinateRows.right.left
          (unary_append_closed coordinateRows.right.right.left
            (unary_append_closed coordinateRows.right.right.right.left antisymUnary))))
      (hsame_symm ledgerRoute)
  have targetLedger : hsame target ledger := targetRoute
  have targetUnary : UnaryHistory target := unary_transport ledgerUnary (hsame_symm targetLedger)
  exact ⟨targetUnary, targetLedger, coordinateRows.right.right.left,
    coordinateRows.right.right.right.left⟩

theorem DiffFormRootConsumerEntry_derivative_boundary
    {degree probe tensor scalar antisym ledger target derivativeBoundary : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont ledger BHist.Empty target ->
            Cont tensor scalar derivativeBoundary ->
              UnaryHistory tensor ∧ UnaryHistory scalar ∧ UnaryHistory derivativeBoundary ∧
                hsame derivativeBoundary (append tensor scalar) := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute targetRoute
    derivativeRoute
  have carrierRows :=
    DiffFormRootConsumerEntry_carrier degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute targetRoute
  have derivativeUnary : UnaryHistory derivativeBoundary :=
    unary_cont_closed carrierRows.right.right.left carrierRows.right.right.right derivativeRoute
  exact And.intro carrierRows.right.right.left
    (And.intro carrierRows.right.right.right
      (And.intro derivativeUnary derivativeRoute))

end BEDC.Derived.DiffFormUp
