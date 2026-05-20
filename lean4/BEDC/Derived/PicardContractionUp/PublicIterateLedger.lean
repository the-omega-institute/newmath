import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_public_iterate_ledger [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      iterateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus iterateRead ->
        PkgSig bundle iterateRead pkg ->
          UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory iterateRead ∧
            Cont iterates modulus endpoint ∧ Cont iterates modulus iterateRead ∧
              PkgSig bundle name pkg ∧ PkgSig bundle iterateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRead iterateReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have iterateReadUnary : UnaryHistory iterateRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRead
  exact
    ⟨iteratesUnary, modulusUnary, iterateReadUnary, iteratesModulusEndpoint,
      iteratesModulusRead, namePkg, iterateReadPkg⟩

theorem PicardContractionPacket_lean_ratio_ledger_nonexpansion_sync
    [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      nextIterates concatenatedIterates concatenatedEndpoint endpointPrime consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      hsame endpoint nextIterates ->
        Cont iterates nextIterates concatenatedIterates ->
          Cont concatenatedIterates modulus concatenatedEndpoint ->
            Cont concatenatedEndpoint transport routes ->
              hsame concatenatedEndpoint endpointPrime ->
                Cont concatenatedIterates modulus endpointPrime ->
                  Cont concatenatedIterates endpointPrime consumer ->
                    PkgSig bundle consumer pkg ->
                      PicardContractionPacket banach contraction lipschitz concatenatedIterates
                          modulus concatenatedEndpoint transport routes provenance name bundle
                          pkg ∧
                        hsame concatenatedEndpoint endpointPrime ∧
                          UnaryHistory endpointPrime ∧ UnaryHistory consumer ∧
                            Cont concatenatedIterates modulus endpointPrime ∧
                              Cont concatenatedIterates endpointPrime consumer ∧
                                PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro packet sameEndpointNextIterates iteratesNextIteratesConcatenated
    concatenatedIteratesModulusEndpoint concatenatedEndpointTransportRoutes
    sameConcatenatedEndpoint endpointPrimeRoute consumerRoute consumerPkg
  obtain ⟨closedPacket, _sameEndpointNextIterates, concatenatedIteratesUnary,
    concatenatedEndpointUnary⟩ :=
    PicardContractionPacket_finite_iterate_closure packet sameEndpointNextIterates
      iteratesNextIteratesConcatenated concatenatedIteratesModulusEndpoint
      concatenatedEndpointTransportRoutes
  have endpointPrimeUnary : UnaryHistory endpointPrime :=
    unary_transport concatenatedEndpointUnary sameConcatenatedEndpoint
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed concatenatedIteratesUnary endpointPrimeUnary consumerRoute
  exact
    ⟨closedPacket, sameConcatenatedEndpoint, endpointPrimeUnary, consumerUnary,
      endpointPrimeRoute, consumerRoute, consumerPkg⟩

end BEDC.Derived.PicardContractionUp
