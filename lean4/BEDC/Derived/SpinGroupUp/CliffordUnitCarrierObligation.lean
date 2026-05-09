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

theorem SpinGroupRootCarrier_clifford_unit_carrier_obligation [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unitLedger :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont unit BHist.Empty unitLedger ->
        CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
          GroupSingletonCarrier groupWord ∧ UnaryHistory unitLedger ∧ hsame unitLedger unit ∧
            Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier unitCont
  have scope := SpinGroupRootCarrier_source_scope carrier
  have unitLedgerUnary : UnaryHistory unitLedger :=
    unary_cont_closed carrier.left.left unary_empty unitCont
  have unitLedgerSame : hsame unitLedger unit :=
    unitCont
  exact
    And.intro scope.left
      (And.intro scope.right.left
        (And.intro unitLedgerUnary
          (And.intro unitLedgerSame
            (And.intro scope.right.right.right.left scope.right.right.right.right))))

theorem SpinGroupRootCarrier_clifford_unit_source_obligation [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unitLedger :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont unit groupWord unitLedger ->
        CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
          GroupSingletonCarrier groupWord ∧ UnaryHistory unit ∧ UnaryHistory unitLedger ∧
            hsame unitLedger (append unit groupWord) ∧ PkgSig bundle ledger pkg := by
  intro carrier unitCont
  have scope := SpinGroupRootCarrier_source_scope carrier
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm scope.right.left)
  have unitLedgerUnary : UnaryHistory unitLedger :=
    unary_cont_closed scope.left.left groupUnary unitCont
  exact
    And.intro scope.left
      (And.intro scope.right.left
        (And.intro scope.left.left
          (And.intro unitLedgerUnary
            (And.intro unitCont scope.right.right.right.right))))

theorem SpinGroupRootCarrier_clifford_unit_ledger_coverage [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unitLedger
      boundaryLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont unit BHist.Empty unitLedger ->
        Cont unitLedger groupWord boundaryLedger ->
          UnaryHistory unitLedger ∧ UnaryHistory boundaryLedger ∧ hsame unitLedger unit ∧
            hsame boundaryLedger (append unitLedger groupWord) ∧ PkgSig bundle ledger pkg := by
  intro carrier unitCont boundaryCont
  have scope := SpinGroupRootCarrier_source_scope carrier
  have unitLedgerUnary : UnaryHistory unitLedger :=
    unary_cont_closed carrier.left.left unary_empty unitCont
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm scope.right.left)
  have boundaryLedgerUnary : UnaryHistory boundaryLedger :=
    unary_cont_closed unitLedgerUnary groupUnary boundaryCont
  exact
    And.intro unitLedgerUnary
      (And.intro boundaryLedgerUnary
        (And.intro (cont_right_unit_result unitCont)
          (And.intro boundaryCont scope.right.right.right.right)))

end BEDC.Derived.SpinGroupUp
