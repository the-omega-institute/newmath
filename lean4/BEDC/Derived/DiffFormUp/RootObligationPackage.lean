import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormRootCarrierSource_obligation {degree probe tensor scalar antisym ledger : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
            UnaryHistory scalar ∧
              hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ∧
                Cont degree probe tensor ∧ Cont tensor antisym scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact
    ⟨carrierRows.left,
      carrierRows.right.left,
      carrierRows.right.right.left,
      carrierRows.right.right.right.left,
      carrierRows.right.right.right.right,
      tensorRoute,
      scalarRoute⟩

end BEDC.Derived.DiffFormUp
