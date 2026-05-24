import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_root_source_window_checked_handoff [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name request
      step rateSource odeRead newtonRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      UnaryHistory request ->
        Cont iterates contraction step ->
          Cont iterates modulus rateSource ->
            Cont iterates endpoint odeRead ->
              Cont endpoint transport newtonRead ->
                Cont endpoint transport sealRead ->
                  PkgSig bundle request pkg ->
                    PkgSig bundle step pkg ->
                      PkgSig bundle rateSource pkg ->
                        PkgSig bundle odeRead pkg ->
                          PkgSig bundle newtonRead pkg ->
                            PkgSig bundle sealRead pkg ->
                              UnaryHistory banach /\ UnaryHistory contraction /\
                                UnaryHistory lipschitz /\ UnaryHistory iterates /\
                                  UnaryHistory modulus /\ UnaryHistory endpoint /\
                                    UnaryHistory request /\ UnaryHistory step /\
                                      UnaryHistory rateSource /\ UnaryHistory odeRead /\
                                        UnaryHistory newtonRead /\ UnaryHistory sealRead /\
                                          Cont banach contraction lipschitz /\
                                            Cont iterates contraction step /\
                                              Cont iterates modulus rateSource /\
                                                Cont iterates endpoint odeRead /\
                                                  Cont endpoint transport newtonRead /\
                                                    Cont endpoint transport sealRead /\
                                                      PkgSig bundle name pkg /\
                                                        PkgSig bundle request pkg /\
                                                          PkgSig bundle step pkg /\
                                                            PkgSig bundle rateSource pkg /\
                                                              PkgSig bundle odeRead pkg /\
                                                                PkgSig bundle newtonRead pkg /\
                                                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet requestUnary iteratesContractionStep iteratesModulusRateSource
    iteratesEndpointOdeRead endpointTransportNewtonRead endpointTransportSealRead requestPkg
    stepPkg rateSourcePkg odeReadPkg newtonReadPkg sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeRead
  have newtonReadUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewtonRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary, endpointUnary,
      requestUnary, stepUnary, rateSourceUnary, odeReadUnary, newtonReadUnary, sealReadUnary,
      banachContractionLipschitz, iteratesContractionStep, iteratesModulusRateSource,
      iteratesEndpointOdeRead, endpointTransportNewtonRead, endpointTransportSealRead,
      namePkg, requestPkg, stepPkg, rateSourcePkg, odeReadPkg, newtonReadPkg, sealReadPkg⟩

theorem PicardContractionRootSourceWindowPacket_downstream_handoff_exhaustion
    [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      request rateSource odeRead newtonRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionRootSourceWindowPacket banach contraction lipschitz iterates modulus
        endpoint transport routes provenance name request bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont rateSource endpoint routes ->
          Cont iterates endpoint odeRead ->
            Cont endpoint transport newtonRead ->
              Cont endpoint transport realRead ->
                PkgSig bundle rateSource pkg ->
                  PkgSig bundle odeRead pkg ->
                    PkgSig bundle newtonRead pkg ->
                      PkgSig bundle realRead pkg ->
                        UnaryHistory request /\ UnaryHistory rateSource /\
                          UnaryHistory odeRead /\ UnaryHistory newtonRead /\
                            UnaryHistory realRead /\ Cont iterates modulus rateSource /\
                              Cont rateSource endpoint routes /\ Cont iterates endpoint odeRead /\
                                Cont endpoint transport newtonRead /\
                                  Cont endpoint transport realRead /\ PkgSig bundle name pkg /\
                                    PkgSig bundle rateSource pkg /\ PkgSig bundle odeRead pkg /\
                                      PkgSig bundle newtonRead pkg /\
                                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro rootPacket iteratesModulusRateSource rateSourceEndpointRoutes iteratesEndpointOdeRead
    endpointTransportNewtonRead endpointTransportRealRead rateSourcePkg odeReadPkg newtonReadPkg
    realReadPkg
  obtain ⟨picardPacket, requestUnary⟩ := rootPacket
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := picardPacket
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeRead
  have newtonReadUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewtonRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportRealRead
  exact
    ⟨requestUnary, rateSourceUnary, odeReadUnary, newtonReadUnary, realReadUnary,
      iteratesModulusRateSource, rateSourceEndpointRoutes, iteratesEndpointOdeRead,
      endpointTransportNewtonRead, endpointTransportRealRead, namePkg, rateSourcePkg,
      odeReadPkg, newtonReadPkg, realReadPkg⟩

theorem PicardContractionRootSourceWindowPacket_determinacy [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      request rateSource odeRead newtonRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionRootSourceWindowPacket banach contraction lipschitz iterates modulus
        endpoint transport routes provenance name request bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont iterates endpoint odeRead ->
          Cont endpoint transport newtonRead ->
            Cont endpoint transport realRead ->
              PkgSig bundle rateSource pkg ->
                PkgSig bundle odeRead pkg ->
                  PkgSig bundle newtonRead pkg ->
                    PkgSig bundle realRead pkg ->
                      UnaryHistory request /\ UnaryHistory rateSource /\
                        UnaryHistory odeRead /\ UnaryHistory newtonRead /\
                          UnaryHistory realRead /\ Cont iterates modulus rateSource /\
                            Cont iterates endpoint odeRead /\
                              Cont endpoint transport newtonRead /\
                                Cont endpoint transport realRead /\ PkgSig bundle name pkg /\
                                  PkgSig bundle rateSource pkg /\ PkgSig bundle odeRead pkg /\
                                    PkgSig bundle newtonRead pkg /\
                                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro rootPacket iteratesModulusRateSource iteratesEndpointOdeRead
    endpointTransportNewtonRead endpointTransportRealRead rateSourcePkg odeReadPkg newtonReadPkg
    realReadPkg
  obtain ⟨picardPacket, requestUnary⟩ := rootPacket
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := picardPacket
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeRead
  have newtonReadUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewtonRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportRealRead
  exact
    ⟨requestUnary, rateSourceUnary, odeReadUnary, newtonReadUnary, realReadUnary,
      iteratesModulusRateSource, iteratesEndpointOdeRead, endpointTransportNewtonRead,
      endpointTransportRealRead, namePkg, rateSourcePkg, odeReadPkg, newtonReadPkg,
      realReadPkg⟩

end BEDC.Derived.PicardContractionUp
