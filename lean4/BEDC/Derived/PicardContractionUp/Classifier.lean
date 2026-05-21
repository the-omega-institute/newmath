import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PicardContractionClassifier [AskSetup] [PackageSetup]
    (banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      banach' contraction' lipschitz' iterates' modulus' endpoint' transport' routes'
      provenance' name' : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame
  PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
      routes provenance name bundle pkg ∧
    PicardContractionPacket banach' contraction' lipschitz' iterates' modulus' endpoint'
      transport' routes' provenance' name' bundle pkg ∧
    hsame banach banach' ∧ hsame contraction contraction' ∧ hsame lipschitz lipschitz' ∧
    hsame iterates iterates' ∧ hsame modulus modulus' ∧ hsame endpoint endpoint' ∧
    hsame transport transport' ∧ hsame routes routes' ∧ hsame provenance provenance' ∧
    hsame name name'

theorem PicardContractionClassifier_endpoint_package_surface [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      banach' contraction' lipschitz' iterates' modulus' endpoint' transport' routes'
      provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionClassifier banach contraction lipschitz iterates modulus endpoint
        transport routes provenance name banach' contraction' lipschitz' iterates' modulus'
        endpoint' transport' routes' provenance' name' bundle pkg →
      UnaryHistory endpoint ∧ UnaryHistory endpoint' ∧ hsame endpoint endpoint' ∧
        Cont iterates modulus endpoint ∧ Cont iterates' modulus' endpoint' ∧
        PkgSig bundle name pkg ∧ PkgSig bundle name' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro classifier
  obtain
    ⟨packet, packet', _sameBanach, _sameContraction, _sameLipschitz, _sameIterates,
      _sameModulus, sameEndpoint, _sameTransport, _sameRoutes, _sameProvenance,
      _sameName⟩ := classifier
  obtain
    ⟨_banachUnary, _contractionUnary, _lipschitzUnary, _iteratesUnary, _modulusUnary,
      endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
      _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
      _routesProvenanceName, namePkg⟩ := packet
  obtain
    ⟨_banachUnary', _contractionUnary', _lipschitzUnary', _iteratesUnary',
      _modulusUnary', endpointUnary', _transportUnary', _routesUnary', _provenanceUnary',
      _nameUnary', _banachContractionLipschitz', iteratesModulusEndpoint',
      _endpointTransportRoutes', _routesProvenanceName', namePkg'⟩ := packet'
  exact
    ⟨endpointUnary, endpointUnary', sameEndpoint, iteratesModulusEndpoint,
      iteratesModulusEndpoint', namePkg, namePkg'⟩

end BEDC.Derived.PicardContractionUp
