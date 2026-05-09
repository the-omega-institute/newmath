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

end BEDC.Derived.SpinGroupUp
