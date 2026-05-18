import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_downstream_modulus_exposure [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      modulusRead endpointRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus modulusRead ->
        Cont modulusRead endpoint endpointRead ->
          Cont endpointRead routes downstream ->
            PkgSig bundle downstream pkg ->
              UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                  UnaryHistory modulusRead ∧ UnaryHistory endpointRead ∧
                    UnaryHistory downstream ∧ Cont banach contraction lipschitz ∧
                      Cont iterates modulus modulusRead ∧
                        Cont modulusRead endpoint endpointRead ∧
                          Cont endpointRead routes downstream ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesModulusRead modulusReadEndpointRead endpointReadRoutesDownstream
    downstreamPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRead
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed modulusReadUnary endpointUnary modulusReadEndpointRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed endpointReadUnary routesUnary endpointReadRoutesDownstream
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, modulusReadUnary, endpointReadUnary, downstreamUnary,
      banachContractionLipschitz, iteratesModulusRead, modulusReadEndpointRead,
      endpointReadRoutesDownstream, namePkg, downstreamPkg⟩

end BEDC.Derived.PicardContractionUp
