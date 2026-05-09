import BEDC.Derived.RepresentationRingUp

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentationRingBHistRepresentationPacket_operation_ledger_coverage [AskSetup]
    [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint directSumEndpoint
      tensorEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      Cont reps directSum directSumEndpoint ->
        Cont reps tensor tensorEndpoint ->
          UnaryHistory directSumEndpoint ∧ UnaryHistory tensorEndpoint ∧
            hsame directSumEndpoint (append reps directSum) ∧
              hsame tensorEndpoint (append reps tensor) ∧
                hsame endpoint (append ledger tensor) ∧ PkgSig bundle endpoint pkg := by
  intro packet directSumRow tensorRow
  have boundary :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary packet
  have directSumEndpointUnary : UnaryHistory directSumEndpoint :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.left directSumRow
  have tensorEndpointUnary : UnaryHistory tensorEndpoint :=
    unary_cont_closed boundary.right.right.left boundary.right.right.right.right.left tensorRow
  exact And.intro directSumEndpointUnary
    (And.intro tensorEndpointUnary
      (And.intro directSumRow
        (And.intro tensorRow
          (And.intro boundary.right.right.right.right.right.right.right.right.right.right.left
            boundary.right.right.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.RepresentationRingUp
