import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_group_interface_boundary [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger groupConsumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont groupWord BHist.Empty groupConsumer ->
        GroupSingletonCarrier groupWord ∧ UnaryHistory groupConsumer ∧
          hsame groupConsumer groupWord ∧ PkgSig bundle ledger pkg := by
  intro carrier groupConsumerRow
  have scope := SpinGroupRootCarrier_source_scope carrier
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm scope.right.left)
  have groupConsumerUnary : UnaryHistory groupConsumer :=
    unary_cont_closed groupUnary unary_empty groupConsumerRow
  exact And.intro scope.right.left
    (And.intro groupConsumerUnary
      (And.intro (cont_right_unit_result groupConsumerRow) scope.right.right.right.right))

end BEDC.Derived.SpinGroupUp
