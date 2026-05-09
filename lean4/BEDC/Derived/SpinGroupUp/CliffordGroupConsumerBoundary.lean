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

theorem SpinGroupRootCarrier_clifford_group_consumer_boundary [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger
      consumerLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont spinEndpoint groupWord consumerLedger ->
        CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
          GroupSingletonCarrier groupWord ∧ UnaryHistory consumerLedger ∧
            hsame consumerLedger (append spinEndpoint groupWord) ∧
              Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier consumerRow
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm sourceScope.right.left)
  have consumerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed sourceScope.right.right.left groupUnary consumerRow
  exact
    ⟨sourceScope.left, sourceScope.right.left, consumerUnary, consumerRow,
      sourceScope.right.right.right.left, sourceScope.right.right.right.right⟩

theorem SpinGroupRootCarrier_group_consumer_boundary [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger row : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame row spinEndpoint ->
        CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
          GroupSingletonCarrier groupWord ∧ UnaryHistory row ∧ UnaryHistory spinEndpoint ∧
            Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier sameRow
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have rowUnary : UnaryHistory row :=
    unary_transport sourceScope.right.right.left (hsame_symm sameRow)
  exact
    ⟨sourceScope.left, sourceScope.right.left, rowUnary, sourceScope.right.right.left,
      sourceScope.right.right.right.left, sourceScope.right.right.right.right⟩

end BEDC.Derived.SpinGroupUp
