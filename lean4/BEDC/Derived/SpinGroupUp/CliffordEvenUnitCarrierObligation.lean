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

theorem SpinGroupRootCarrier_clifford_even_unit_carrier_obligation [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unitEndpoint
      unitLedger thresholdLedger : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      Cont unit BHist.Empty unitEndpoint ->
        Cont unitEndpoint groupWord unitLedger ->
          Cont product groupWord thresholdLedger ->
            CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
              GroupSingletonCarrier groupWord ∧ UnaryHistory unitEndpoint ∧
                UnaryHistory unitLedger ∧ UnaryHistory thresholdLedger ∧
                  hsame unitLedger (append unitEndpoint groupWord) ∧
                    hsame thresholdLedger (append product groupWord) ∧
                      PkgSig bundle ledger pkg := by
  intro carrier unitEndpointRow unitLedgerRow thresholdRow
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have unitLift := SpinGroupRootCarrier_unit_lift carrier unitEndpointRow unitLedgerRow
  have threshold := SpinGroupRootCarrier_threshold_obligation_triple carrier thresholdRow
  exact
    And.intro sourceScope.left
      (And.intro sourceScope.right.left
        (And.intro unitLift.right.left
            (And.intro unitLift.right.right.left
              (And.intro threshold.right.right.right.left
              (And.intro unitLift.right.right.right.right
                (And.intro threshold.right.right.right.right.right.right.right.right.right.left
                  sourceScope.right.right.right.right))))))

end BEDC.Derived.SpinGroupUp
