import BEDC.Derived.SpinGroupUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.SpinGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_spin_boundary_inclusion_transport [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger product' boundary'
      spinEndpoint' consumerLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame product product' ->
        hsame boundary boundary' ->
          Cont product' boundary' cliffordEndpoint ->
            Cont cliffordEndpoint groupWord spinEndpoint' ->
              Cont spinEndpoint' BHist.Empty consumerLedger ->
                SpinGroupRootCarrier unit vector product' boundary' cliffordEndpoint groupWord
                    spinEndpoint' ledger bundle pkg ∧
                  hsame spinEndpoint spinEndpoint' ∧ UnaryHistory consumerLedger ∧
                    hsame consumerLedger spinEndpoint' ∧ PkgSig bundle ledger pkg := by
  intro carrier sameProduct sameBoundary boundaryRow spinRow consumerRow
  have transported :=
    SpinGroupRootCarrier_public_boundary_transport_stability carrier sameProduct sameBoundary
      boundaryRow spinRow
  have transportedScope :=
    SpinGroupRootCarrier_source_scope transported.left
  have consumerUnary : UnaryHistory consumerLedger :=
    unary_cont_closed transportedScope.right.right.left unary_empty consumerRow
  have consumerSame : hsame consumerLedger spinEndpoint' :=
    cont_right_unit_result consumerRow
  exact And.intro transported.left
    (And.intro transported.right
      (And.intro consumerUnary
        (And.intro consumerSame transportedScope.right.right.right.right)))

end BEDC.Derived.SpinGroupUp
