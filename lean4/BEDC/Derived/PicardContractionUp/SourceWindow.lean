import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_source_window_formal_target [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sealRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont endpoint transport sealRead ->
        Cont iterates endpoint consumer ->
          PkgSig bundle sealRead pkg ->
            PkgSig bundle consumer pkg ->
              UnaryHistory banach /\ UnaryHistory contraction /\ UnaryHistory lipschitz /\
                UnaryHistory iterates /\ UnaryHistory modulus /\ UnaryHistory endpoint /\
                  UnaryHistory sealRead /\ UnaryHistory consumer /\
                    Cont banach contraction lipschitz /\ Cont iterates modulus endpoint /\
                      Cont endpoint transport sealRead /\ Cont iterates endpoint consumer /\
                        PkgSig bundle name pkg /\ PkgSig bundle sealRead pkg /\
                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet endpointTransportSealRead iteratesEndpointConsumer sealReadPkg consumerPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, sealReadUnary, consumerUnary, banachContractionLipschitz,
      iteratesModulusEndpoint, endpointTransportSealRead, iteratesEndpointConsumer, namePkg,
      sealReadPkg, consumerPkg⟩

end BEDC.Derived.PicardContractionUp
