import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormRootConsumerExport_no_extra_laws
    {degree probe tensor scalar antisym ledger tail : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          hsame ledger (BHist.e0 tail) -> False := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute zeroRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have targetUnary :
      UnaryHistory (append degree (append probe (append tensor (append scalar antisym)))) :=
    unary_append_closed coordinateRows.left
      (unary_append_closed coordinateRows.right.left
        (unary_append_closed coordinateRows.right.right.left
          (unary_append_closed coordinateRows.right.right.right.left antisymUnary)))
  have ledgerUnary : UnaryHistory ledger :=
    unary_transport targetUnary (hsame_symm ledgerRoute)
  exact unary_no_zero_extension (unary_transport ledgerUnary zeroRoute)

end BEDC.Derived.DiffFormUp
