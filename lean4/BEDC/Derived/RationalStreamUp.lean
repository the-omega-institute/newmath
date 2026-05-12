import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RationalStreamPacket [AskSetup] [PackageSetup]
    (index schedule point classifier transport window provenance name endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory index ∧ UnaryHistory schedule ∧ UnaryHistory point ∧
    UnaryHistory classifier ∧ Cont index schedule transport ∧
      Cont point classifier window ∧ Cont transport window provenance ∧
        Cont provenance name endpoint ∧ PkgSig bundle endpoint pkg

theorem RationalStreamPacket_finite_window_transport [AskSetup] [PackageSetup]
    {index schedule point classifier transport window provenance name endpoint index' schedule'
      point' classifier' transport' window' provenance' name' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalStreamPacket index schedule point classifier transport window provenance name endpoint
        bundle pkg ->
      hsame index index' -> hsame schedule schedule' -> hsame point point' ->
        hsame classifier classifier' -> hsame name name' -> Cont index' schedule' transport' ->
          Cont point' classifier' window' -> Cont transport' window' provenance' ->
            Cont provenance' name' endpoint' -> PkgSig bundle endpoint' pkg ->
              RationalStreamPacket index' schedule' point' classifier' transport' window'
                  provenance' name' endpoint' bundle pkg ∧
                hsame transport transport' ∧ hsame window window' ∧
                  hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro packet sameIndex sameSchedule samePoint sameClassifier sameName transportRow' windowRow'
    provenanceRow' endpointRow' pkgSig'
  have transportRow : Cont index schedule transport :=
    packet.right.right.right.right.left
  have windowRow : Cont point classifier window :=
    packet.right.right.right.right.right.left
  have provenanceRow : Cont transport window provenance :=
    packet.right.right.right.right.right.right.left
  have endpointRow : Cont provenance name endpoint :=
    packet.right.right.right.right.right.right.right.left
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameIndex sameSchedule transportRow transportRow'
  have sameWindow : hsame window window' :=
    cont_respects_hsame samePoint sameClassifier windowRow windowRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameWindow provenanceRow provenanceRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameName endpointRow endpointRow'
  have transported :
      RationalStreamPacket index' schedule' point' classifier' transport' window'
          provenance' name' endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameIndex,
      unary_transport packet.right.left sameSchedule,
      unary_transport packet.right.right.left samePoint,
      unary_transport packet.right.right.right.left sameClassifier,
      transportRow',
      windowRow',
      provenanceRow',
      endpointRow',
      pkgSig'⟩
  exact And.intro transported
    (And.intro sameTransport
      (And.intro sameWindow
        (And.intro sameProvenance sameEndpoint)))

end BEDC.Derived.RationalStreamUp
