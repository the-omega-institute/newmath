import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionRootSourceWindowPacket_modulus_consumer_lock [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name request
      rateSource sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionRootSourceWindowPacket banach contraction lipschitz iterates modulus
        endpoint transport routes provenance name request bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont rateSource endpoint routes ->
          Cont endpoint transport sealRead ->
            PkgSig bundle rateSource pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                  UnaryHistory rateSource ∧ UnaryHistory sealRead ∧
                    Cont iterates modulus rateSource ∧ Cont rateSource endpoint routes ∧
                      Cont endpoint transport sealRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle rateSource pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro rootPacket iteratesModulusRateSource rateSourceEndpointRoutes endpointTransportSealRead
    rateSourcePkg sealReadPkg
  obtain ⟨picardPacket, _requestUnary⟩ := rootPacket
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := picardPacket
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨iteratesUnary, modulusUnary, endpointUnary, rateSourceUnary, sealReadUnary,
      iteratesModulusRateSource, rateSourceEndpointRoutes, endpointTransportSealRead, namePkg,
      rateSourcePkg, sealReadPkg⟩

end BEDC.Derived.PicardContractionUp
