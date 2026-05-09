import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.CliffordUp
open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_lift_parity_ledger [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger
      parityLedger projectionLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont spinEndpoint groupWord parityLedger ->
        Cont parityLedger BHist.Empty projectionLedger ->
          UnaryHistory spinEndpoint ∧ UnaryHistory parityLedger ∧
            UnaryHistory projectionLedger ∧ hsame parityLedger (append spinEndpoint groupWord) ∧
              hsame projectionLedger parityLedger ∧ PkgSig bundle ledger pkg := by
  intro carrier parityRow projectionRow
  have sourceScope :=
    SpinGroupRootCarrier_source_scope carrier
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm sourceScope.right.left)
  have parityUnary : UnaryHistory parityLedger :=
    unary_cont_closed sourceScope.right.right.left groupUnary parityRow
  have projectionUnary : UnaryHistory projectionLedger :=
    unary_cont_closed parityUnary unary_empty projectionRow
  exact
    ⟨sourceScope.right.right.left, parityUnary, projectionUnary, parityRow,
      cont_right_unit_result projectionRow, sourceScope.right.right.right.right⟩

end BEDC.Derived.SpinGroupUp
