import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.HodgeBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HodgeBridgeBHistSourcePacket [AskSetup] [PackageSetup]
    (derham cohomology projector bidegree lefschetz readback transport provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derham ∧ UnaryHistory cohomology ∧ UnaryHistory projector ∧
    UnaryHistory bidegree ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont derham projector readback ∧ Cont readback bidegree lefschetz ∧
        Cont provenance lefschetz endpoint ∧ PkgSig bundle endpoint pkg

theorem HodgeBridgeBHistSourcePacket_source_dependency_surface [AskSetup] [PackageSetup]
    {derham cohomology projector bidegree lefschetz readback transport provenance endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HodgeBridgeBHistSourcePacket derham cohomology projector bidegree lefschetz readback
        transport provenance endpoint bundle pkg ->
      UnaryHistory derham ∧ UnaryHistory cohomology ∧ UnaryHistory projector ∧
        UnaryHistory bidegree ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
          UnaryHistory readback ∧ UnaryHistory lefschetz ∧ UnaryHistory endpoint ∧
            Cont derham projector readback ∧ Cont readback bidegree lefschetz ∧
              Cont provenance lefschetz endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have projectorUnary : UnaryHistory projector := packet.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed packet.left projectorUnary packet.right.right.right.right.right.right.left
  have bidegreeUnary : UnaryHistory bidegree := packet.right.right.right.left
  have lefschetzUnary : UnaryHistory lefschetz :=
    unary_cont_closed readbackUnary bidegreeUnary
      packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary lefschetzUnary
      packet.right.right.right.right.right.right.right.right.left
  exact
    ⟨packet.left, packet.right.left, projectorUnary, bidegreeUnary,
      packet.right.right.right.right.left, provenanceUnary, readbackUnary, lefschetzUnary,
      endpointUnary, packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

theorem HodgeBridgeBHistSourcePacket_harmonic_projector_classifier_stability
    [AskSetup] [PackageSetup]
    {derham derham' cohomology projector projector' bidegree bidegree'
      lefschetz lefschetz' readback readback' transport provenance provenance'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HodgeBridgeBHistSourcePacket derham cohomology projector bidegree lefschetz
        readback transport provenance endpoint bundle pkg ->
      hsame derham derham' ->
      hsame projector projector' ->
      hsame bidegree bidegree' ->
      hsame provenance provenance' ->
      Cont derham' projector' readback' ->
      Cont readback' bidegree' lefschetz' ->
      Cont provenance' lefschetz' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      HodgeBridgeBHistSourcePacket derham' cohomology projector' bidegree'
          lefschetz' readback' transport provenance' endpoint' bundle pkg ∧
        hsame readback readback' ∧ hsame lefschetz lefschetz' ∧
          hsame endpoint endpoint' := by
  intro packet sameDerham sameProjector sameBidegree sameProvenance readbackCont'
    lefschetzCont' endpointCont' pkgSig'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameDerham sameProjector
      packet.right.right.right.right.right.right.left readbackCont'
  have sameLefschetz : hsame lefschetz lefschetz' :=
    cont_respects_hsame sameReadback sameBidegree
      packet.right.right.right.right.right.right.right.left lefschetzCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameLefschetz
      packet.right.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨unary_transport packet.left sameDerham, packet.right.left,
        unary_transport packet.right.right.left sameProjector,
        unary_transport packet.right.right.right.left sameBidegree,
        packet.right.right.right.right.left,
        unary_transport packet.right.right.right.right.right.left sameProvenance,
        readbackCont', lefschetzCont', endpointCont', pkgSig'⟩,
      sameReadback, sameLefschetz, sameEndpoint⟩

theorem HodgeBridgeBHistSourcePacket_public_certificate_handoff [AskSetup] [PackageSetup]
    {derham derham' cohomology projector projector' bidegree bidegree'
      lefschetz lefschetz' readback readback' transport provenance provenance'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HodgeBridgeBHistSourcePacket derham cohomology projector bidegree lefschetz
        readback transport provenance endpoint bundle pkg ->
      hsame derham derham' ->
      hsame projector projector' ->
      hsame bidegree bidegree' ->
      hsame provenance provenance' ->
      Cont derham' projector' readback' ->
      Cont readback' bidegree' lefschetz' ->
      Cont provenance' lefschetz' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      HodgeBridgeBHistSourcePacket derham' cohomology projector' bidegree'
          lefschetz' readback' transport provenance' endpoint' bundle pkg ∧
        hsame readback readback' ∧ hsame lefschetz lefschetz' ∧
          hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg := by
  intro packet sameDerham sameProjector sameBidegree sameProvenance readbackCont'
    lefschetzCont' endpointCont' pkgSig'
  have stability :=
    HodgeBridgeBHistSourcePacket_harmonic_projector_classifier_stability
      packet sameDerham sameProjector sameBidegree sameProvenance readbackCont'
      lefschetzCont' endpointCont' pkgSig'
  exact
    ⟨stability.left, stability.right.left, stability.right.right.left,
      stability.right.right.right, packet.right.right.right.right.right.right.right.right.right⟩

theorem HodgeBridgeBHistSourcePacket_shared_projector_readback_exactness
    [AskSetup] [PackageSetup]
    {derham derham' cohomology projector projector' bidegree bidegree' lefschetz
      lefschetz' readback readback' transport provenance provenance' endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HodgeBridgeBHistSourcePacket derham cohomology projector bidegree lefschetz readback
        transport provenance endpoint bundle pkg ->
      hsame derham derham' ->
      hsame projector projector' ->
      hsame bidegree bidegree' ->
      hsame provenance provenance' ->
      Cont derham' projector' readback' ->
      Cont readback' bidegree' lefschetz' ->
      Cont provenance' lefschetz' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      HodgeBridgeBHistSourcePacket derham' cohomology projector' bidegree'
          lefschetz' readback' transport provenance' endpoint' bundle pkg ∧
        hsame readback readback' ∧ hsame lefschetz lefschetz' ∧
          hsame endpoint endpoint' ∧ UnaryHistory readback' ∧ UnaryHistory lefschetz' ∧
            UnaryHistory endpoint' := by
  intro packet sameDerham sameProjector sameBidegree sameProvenance readbackCont'
    lefschetzCont' endpointCont' pkgSig'
  have stability :=
    HodgeBridgeBHistSourcePacket_harmonic_projector_classifier_stability
      packet sameDerham sameProjector sameBidegree sameProvenance readbackCont'
      lefschetzCont' endpointCont' pkgSig'
  have surface :=
    HodgeBridgeBHistSourcePacket_source_dependency_surface stability.left
  exact
    ⟨stability.left, stability.right.left, stability.right.right.left,
      stability.right.right.right, surface.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.left,
      surface.right.right.right.right.right.right.right.right.left⟩

end BEDC.Derived.HodgeBridgeUp
