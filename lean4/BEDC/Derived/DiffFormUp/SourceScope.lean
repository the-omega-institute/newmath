import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormBHistCarrier_source_scope
    {degree probe tensor scalar antisym ledger : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
            UnaryHistory scalar ∧ Cont degree probe tensor ∧ Cont tensor antisym scalar ∧
              hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact And.intro coordinateRows.left
    (And.intro coordinateRows.right.left
      (And.intro coordinateRows.right.right.left
        (And.intro coordinateRows.right.right.right.left
          (And.intro tensorRoute
            (And.intro scalarRoute coordinateRows.right.right.right.right)))))

end BEDC.Derived.DiffFormUp
