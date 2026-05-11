import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DiffFormBHistCarrier_support_obligation {degree probe tensor scalar antisym ledger : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
            UnaryHistory scalar ∧ UnaryHistory antisym ∧
              hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ∧
                Cont degree probe tensor ∧ Cont tensor antisym scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have rows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact And.intro rows.left
    (And.intro rows.right.left
      (And.intro rows.right.right.left
        (And.intro rows.right.right.right.left
          (And.intro antisymUnary
            (And.intro rows.right.right.right.right
              (And.intro tensorRoute scalarRoute))))))

end BEDC.Derived.DiffFormUp
