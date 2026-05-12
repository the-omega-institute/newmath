import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachFixedPointUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BanachFixedPointPacket [AskSetup] [PackageSetup]
    (banach distance contraction ratio iterate modulus handoff endpoint transport continuation
      provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory banach ∧ UnaryHistory distance ∧ UnaryHistory contraction ∧
    UnaryHistory ratio ∧ UnaryHistory iterate ∧ UnaryHistory modulus ∧
      UnaryHistory handoff ∧ UnaryHistory endpoint ∧ UnaryHistory transport ∧
        UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
          Cont banach distance contraction ∧ Cont contraction ratio iterate ∧
            Cont iterate modulus handoff ∧ Cont handoff transport continuation ∧
              Cont continuation provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem BanachFixedPointPacket_namecert_obligations [AskSetup] [PackageSetup]
    {banach distance contraction ratio iterate modulus handoff endpoint transport continuation
      provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachFixedPointPacket banach distance contraction ratio iterate modulus handoff endpoint
        transport continuation provenance nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              BanachFixedPointPacket banach distance contraction ratio iterate modulus handoff
                endpoint transport continuation provenance nameCert bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        UnaryHistory banach ∧ UnaryHistory distance ∧ UnaryHistory contraction ∧
          UnaryHistory ratio ∧ UnaryHistory iterate ∧ UnaryHistory modulus ∧
            UnaryHistory handoff ∧ UnaryHistory endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have packetWitness := packet
  obtain ⟨banachUnary, distanceUnary, contractionUnary, ratioUnary, iterateUnary,
    modulusUnary, handoffUnary, endpointUnary, _transportUnary, _continuationUnary,
    _provenanceUnary, _nameCertUnary, _banachDistanceContraction,
    _contractionRatioIterate, _iterateModulusHandoff, _handoffTransportContinuation,
    _continuationProvenanceEndpoint, endpointPkg⟩ := packet
  have sourceEndpoint :
      (fun row : BHist =>
        hsame row endpoint ∧
          BanachFixedPointPacket banach distance contraction ratio iterate modulus handoff
            endpoint transport continuation provenance nameCert bundle pkg) endpoint := by
    exact ⟨hsame_refl endpoint, packetWitness⟩
  have core :
      NameCert
        (fun row : BHist =>
          hsame row endpoint ∧
            BanachFixedPointPacket banach distance contraction ratio iterate modulus handoff
              endpoint transport continuation provenance nameCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              BanachFixedPointPacket banach distance contraction ratio iterate modulus handoff
                endpoint transport continuation provenance nameCert bundle pkg)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, endpointPkg⟩
    }
  exact
    ⟨cert, banachUnary, distanceUnary, contractionUnary, ratioUnary, iterateUnary,
      modulusUnary, handoffUnary, endpointUnary, endpointPkg⟩

theorem BanachFixedPointPacket_cauchy_handoff [AskSetup] [PackageSetup]
    {banach distance contraction ratio iterate modulus handoff endpoint transport continuation
      provenance nameCert exportRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachFixedPointPacket banach distance contraction ratio iterate modulus handoff endpoint
        transport continuation provenance nameCert bundle pkg ->
      Cont modulus handoff exportRow ->
        PkgSig bundle exportRow pkg ->
          UnaryHistory iterate ∧ UnaryHistory modulus ∧ UnaryHistory handoff ∧
            UnaryHistory exportRow ∧ Cont contraction ratio iterate ∧
              Cont iterate modulus handoff ∧ Cont modulus handoff exportRow ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle exportRow pkg := by
  intro packet exportRoute exportPkg
  obtain ⟨_banachUnary, _distanceUnary, contractionUnary, ratioUnary, iterateUnary,
    modulusUnary, handoffUnary, _endpointUnary, _transportUnary, _continuationUnary,
    _provenanceUnary, _nameCertUnary, _banachDistanceContraction,
    contractionRatioIterate, iterateModulusHandoff, _handoffTransportContinuation,
    _continuationProvenanceEndpoint, endpointPkg⟩ := packet
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed modulusUnary handoffUnary exportRoute
  exact
    ⟨iterateUnary, modulusUnary, handoffUnary, exportUnary, contractionRatioIterate,
      iterateModulusHandoff, exportRoute, endpointPkg, exportPkg⟩

theorem BanachFixedPointPacket_iteration_ledger [AskSetup] [PackageSetup]
    {banach distance contraction ratio iterate modulus handoff endpoint transport continuation
      provenance nameCert stepRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachFixedPointPacket banach distance contraction ratio iterate modulus handoff endpoint
        transport continuation provenance nameCert bundle pkg ->
      Cont iterate stepRow handoff ->
        UnaryHistory stepRow ->
          UnaryHistory banach ∧ UnaryHistory distance ∧ UnaryHistory contraction ∧
            UnaryHistory ratio ∧ UnaryHistory iterate ∧ UnaryHistory stepRow ∧
              Cont contraction ratio iterate ∧ Cont iterate stepRow handoff ∧
                PkgSig bundle endpoint pkg := by
  intro packet iterateStepHandoff stepRowUnary
  obtain ⟨banachUnary, distanceUnary, contractionUnary, ratioUnary, iterateUnary,
    _modulusUnary, _handoffUnary, _endpointUnary, _transportUnary, _continuationUnary,
    _provenanceUnary, _nameCertUnary, _banachDistanceContraction, contractionRatioIterate,
    _iterateModulusHandoff, _handoffTransportContinuation, _continuationProvenanceEndpoint,
    endpointPkg⟩ := packet
  exact
    ⟨banachUnary, distanceUnary, contractionUnary, ratioUnary, iterateUnary, stepRowUnary,
      contractionRatioIterate, iterateStepHandoff, endpointPkg⟩

end BEDC.Derived.BanachFixedPointUp
