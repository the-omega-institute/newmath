import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GeomQuantizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GeomQuantizationBHistSourcePacket [AskSetup] [PackageSetup]
    (symplectic hilbert line polarisation metaplectic readback transport provenance endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory symplectic ∧ UnaryHistory hilbert ∧ UnaryHistory line ∧
    UnaryHistory polarisation ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
      Cont symplectic line readback ∧ Cont readback polarisation metaplectic ∧
        Cont provenance metaplectic endpoint ∧ PkgSig bundle endpoint pkg

theorem GeomQuantizationBHistSourcePacket_source_dependency_surface
    [AskSetup] [PackageSetup]
    {symplectic hilbert line polarisation metaplectic readback transport provenance endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeomQuantizationBHistSourcePacket symplectic hilbert line polarisation metaplectic
        readback transport provenance endpoint bundle pkg ->
      UnaryHistory symplectic ∧ UnaryHistory hilbert ∧ UnaryHistory line ∧
        UnaryHistory polarisation ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
          UnaryHistory readback ∧ UnaryHistory metaplectic ∧ UnaryHistory endpoint ∧
            Cont symplectic line readback ∧ Cont readback polarisation metaplectic ∧
              Cont provenance metaplectic endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have lineUnary : UnaryHistory line := packet.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed packet.left lineUnary packet.right.right.right.right.right.right.left
  have polarisationUnary : UnaryHistory polarisation := packet.right.right.right.left
  have metaplecticUnary : UnaryHistory metaplectic :=
    unary_cont_closed readbackUnary polarisationUnary
      packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary metaplecticUnary
      packet.right.right.right.right.right.right.right.right.left
  exact
    ⟨packet.left, packet.right.left, lineUnary, polarisationUnary,
      packet.right.right.right.right.left, provenanceUnary, readbackUnary, metaplecticUnary,
      endpointUnary, packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

theorem GeomQuantizationBHistSourcePacket_polarisation_classifier_stability
    [AskSetup] [PackageSetup]
    {symplectic symplectic' hilbert line line' polarisation polarisation'
      metaplectic metaplectic' readback readback' transport provenance provenance'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeomQuantizationBHistSourcePacket symplectic hilbert line polarisation metaplectic
        readback transport provenance endpoint bundle pkg ->
      hsame symplectic symplectic' ->
      hsame line line' ->
      hsame polarisation polarisation' ->
      hsame provenance provenance' ->
      Cont symplectic' line' readback' ->
      Cont readback' polarisation' metaplectic' ->
      Cont provenance' metaplectic' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      GeomQuantizationBHistSourcePacket symplectic' hilbert line' polarisation'
          metaplectic' readback' transport provenance' endpoint' bundle pkg ∧
        hsame readback readback' ∧ hsame metaplectic metaplectic' ∧
          hsame endpoint endpoint' := by
  intro packet sameSymplectic sameLine samePolarisation sameProvenance readbackCont'
    metaplecticCont' endpointCont' pkgSig'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameSymplectic sameLine
      packet.right.right.right.right.right.right.left readbackCont'
  have sameMetaplectic : hsame metaplectic metaplectic' :=
    cont_respects_hsame sameReadback samePolarisation
      packet.right.right.right.right.right.right.right.left metaplecticCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance sameMetaplectic
      packet.right.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨unary_transport packet.left sameSymplectic, packet.right.left,
        unary_transport packet.right.right.left sameLine,
        unary_transport packet.right.right.right.left samePolarisation,
        packet.right.right.right.right.left,
        unary_transport packet.right.right.right.right.right.left sameProvenance,
        readbackCont', metaplecticCont', endpointCont', pkgSig'⟩,
      sameReadback, sameMetaplectic, sameEndpoint⟩

theorem GeomQuantizationBHistSourcePacket_ledger_exactness [AskSetup] [PackageSetup]
    {symplectic hilbert line polarisation metaplectic readback transport provenance endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeomQuantizationBHistSourcePacket symplectic hilbert line polarisation metaplectic
        readback transport provenance endpoint bundle pkg ->
      UnaryHistory symplectic ∧ UnaryHistory hilbert ∧ UnaryHistory line ∧
        UnaryHistory polarisation ∧ UnaryHistory metaplectic ∧ UnaryHistory readback ∧
          UnaryHistory endpoint ∧ hsame readback (append symplectic line) ∧
            hsame metaplectic (append readback polarisation) ∧
              hsame endpoint (append provenance metaplectic) ∧
                PkgSig bundle endpoint pkg := by
  intro packet
  have lineUnary : UnaryHistory line := packet.right.right.left
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed packet.left lineUnary packet.right.right.right.right.right.right.left
  have polarisationUnary : UnaryHistory polarisation := packet.right.right.right.left
  have metaplecticUnary : UnaryHistory metaplectic :=
    unary_cont_closed readbackUnary polarisationUnary
      packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary metaplecticUnary
      packet.right.right.right.right.right.right.right.right.left
  exact
    ⟨packet.left, packet.right.left, lineUnary, polarisationUnary, metaplecticUnary,
      readbackUnary, endpointUnary, packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩
theorem GeomQuantizationBHistSourcePacket_line_ledger_transport_determinacy
    [AskSetup] [PackageSetup]
    {symplectic hilbert line line' polarisation metaplectic metaplectic' readback readback'
      transport provenance endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GeomQuantizationBHistSourcePacket symplectic hilbert line polarisation metaplectic
        readback transport provenance endpoint bundle pkg ->
      hsame line' line -> Cont symplectic line' readback' ->
        Cont readback' polarisation metaplectic' -> Cont provenance metaplectic' endpoint' ->
          hsame readback readback' ∧ hsame metaplectic metaplectic' ∧ hsame endpoint endpoint' ∧
            UnaryHistory line' ∧ UnaryHistory readback' ∧ UnaryHistory metaplectic' ∧
              UnaryHistory endpoint' := by
  intro packet sameLine symplecticLine' readbackPolarisation' provenanceMetaplectic'
  have lineUnary' : UnaryHistory line' :=
    unary_transport packet.right.right.left (hsame_symm sameLine)
  have readbackUnary' : UnaryHistory readback' :=
    unary_cont_closed packet.left lineUnary' symplecticLine'
  have polarisationUnary : UnaryHistory polarisation := packet.right.right.right.left
  have metaplecticUnary' : UnaryHistory metaplectic' :=
    unary_cont_closed readbackUnary' polarisationUnary readbackPolarisation'
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed provenanceUnary metaplecticUnary' provenanceMetaplectic'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame (hsame_refl symplectic) (hsame_symm sameLine)
      packet.right.right.right.right.right.right.left symplecticLine'
  have sameMetaplectic : hsame metaplectic metaplectic' :=
    cont_respects_hsame sameReadback (hsame_refl polarisation)
      packet.right.right.right.right.right.right.right.left readbackPolarisation'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameMetaplectic
      packet.right.right.right.right.right.right.right.right.left provenanceMetaplectic'
  exact
    ⟨sameReadback, sameMetaplectic, sameEndpoint, lineUnary', readbackUnary',
      metaplecticUnary', endpointUnary'⟩

end BEDC.Derived.GeomQuantizationUp
