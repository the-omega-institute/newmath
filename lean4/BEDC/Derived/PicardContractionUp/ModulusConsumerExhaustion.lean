import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_modulus_consumer_exhaustion [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name step
      odeRead realRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates contraction step ->
        Cont iterates endpoint odeRead ->
          Cont endpoint transport realRead ->
            Cont endpoint transport sealRead ->
              PkgSig bundle step pkg ->
                PkgSig bundle odeRead pkg ->
                  PkgSig bundle realRead pkg ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory banach /\ UnaryHistory contraction /\ UnaryHistory lipschitz /\
                        UnaryHistory iterates /\ UnaryHistory modulus /\ UnaryHistory endpoint /\
                          UnaryHistory step /\ UnaryHistory odeRead /\ UnaryHistory realRead /\
                            UnaryHistory sealRead /\ Cont banach contraction lipschitz /\
                              Cont iterates modulus endpoint /\
                                Cont iterates contraction step /\
                                  Cont iterates endpoint odeRead /\
                                    Cont endpoint transport realRead /\
                                      Cont endpoint transport sealRead /\
                                        PkgSig bundle name pkg /\
                                          PkgSig bundle step pkg /\
                                            PkgSig bundle odeRead pkg /\
                                              PkgSig bundle realRead pkg /\
                                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesContractionStep iteratesEndpointOdeRead endpointTransportRealRead
    endpointTransportSealRead stepPkg odeReadPkg realReadPkg sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportRealRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, stepUnary, odeReadUnary, realReadUnary, sealReadUnary,
      banachContractionLipschitz, iteratesModulusEndpoint, iteratesContractionStep,
      iteratesEndpointOdeRead, endpointTransportRealRead, endpointTransportSealRead,
      namePkg, stepPkg, odeReadPkg, realReadPkg, sealReadPkg⟩

end BEDC.Derived.PicardContractionUp
