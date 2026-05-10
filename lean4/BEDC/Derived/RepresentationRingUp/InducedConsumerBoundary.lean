import BEDC.Derived.RepresentationRingUp

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RepresentationRingBHistRepresentationPacket_induced_consumer_boundary [AskSetup]
    [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint inducedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      Cont endpoint reps inducedEndpoint ->
        UnaryHistory inducedEndpoint ∧ hsame inducedEndpoint (append endpoint reps) ∧
          hsame endpoint (append ledger tensor) ∧ PkgSig bundle endpoint pkg := by
  intro packet inducedRow
  have boundary :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary packet
  have inducedUnary : UnaryHistory inducedEndpoint :=
    unary_cont_closed boundary.right.right.right.right.right.right.right.right.left
      packet.right.right.left inducedRow
  exact And.intro inducedUnary
    (And.intro inducedRow
      (And.intro boundary.right.right.right.right.right.right.right.right.right.right.left
        boundary.right.right.right.right.right.right.right.right.right.right.right))

theorem RepresentationRingBHistRepresentationPacket_consumer_boundary [AskSetup] [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint inducedEndpoint
      consumerEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      Cont endpoint reps inducedEndpoint ->
        Cont inducedEndpoint ledger consumerEndpoint ->
          UnaryHistory inducedEndpoint ∧ UnaryHistory consumerEndpoint ∧
            hsame inducedEndpoint (append endpoint reps) ∧
              hsame consumerEndpoint (append inducedEndpoint ledger) ∧
                hsame endpoint (append ledger tensor) ∧ PkgSig bundle endpoint pkg := by
  intro packet inducedRow consumerRow
  have boundary :=
    RepresentationRingBHistRepresentationPacket_carrier_boundary packet
  have inducedUnary : UnaryHistory inducedEndpoint :=
    unary_cont_closed boundary.right.right.right.right.right.right.right.right.left
      packet.right.right.left inducedRow
  have consumerUnary : UnaryHistory consumerEndpoint :=
    unary_cont_closed inducedUnary boundary.right.right.right.right.right.right.right.left
      consumerRow
  exact And.intro inducedUnary
    (And.intro consumerUnary
      (And.intro inducedRow
        (And.intro consumerRow
          (And.intro boundary.right.right.right.right.right.right.right.right.right.right.left
            boundary.right.right.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.RepresentationRingUp
