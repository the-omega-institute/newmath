import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_cauchy_modulus_handoff [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      modulusRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus modulusRead ->
        Cont modulusRead endpoint cauchyRead ->
          PkgSig bundle modulusRead pkg ->
            PkgSig bundle cauchyRead pkg ->
              UnaryHistory modulus ∧ UnaryHistory modulusRead ∧ UnaryHistory cauchyRead ∧
                Cont iterates modulus endpoint ∧ Cont iterates modulus modulusRead ∧
                  Cont modulusRead endpoint cauchyRead ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle modulusRead pkg ∧ PkgSig bundle cauchyRead pkg := by
  intro packet iteratesModulusRead modulusReadEndpointCauchyRead modulusReadPkg cauchyReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRead
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed modulusReadUnary endpointUnary modulusReadEndpointCauchyRead
  exact
    ⟨modulusUnary, modulusReadUnary, cauchyReadUnary, iteratesModulusEndpoint,
      iteratesModulusRead, modulusReadEndpointCauchyRead, namePkg, modulusReadPkg,
      cauchyReadPkg⟩

theorem PicardContractionPacket_public_banach_source_modulus_seal
    [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont endpoint transport sealRead ->
          PkgSig bundle rateSource pkg ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                  UnaryHistory rateSource ∧ UnaryHistory sealRead ∧
                    Cont banach contraction lipschitz ∧ Cont iterates modulus rateSource ∧
                      Cont iterates modulus endpoint ∧ Cont endpoint transport sealRead ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle rateSource pkg ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesModulusRateSource endpointTransportSealRead rateSourcePkg sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, rateSourceUnary, sealReadUnary, banachContractionLipschitz,
      iteratesModulusRateSource, iteratesModulusEndpoint, endpointTransportSealRead,
      namePkg, rateSourcePkg, sealReadPkg⟩

theorem PicardContractionPacket_public_namecert_package [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name step
      odeRead newtonRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates contraction step ->
        Cont iterates endpoint odeRead ->
          Cont endpoint transport newtonRead ->
            Cont endpoint transport sealRead ->
              PkgSig bundle step pkg ->
                PkgSig bundle odeRead pkg ->
                  PkgSig bundle newtonRead pkg ->
                    PkgSig bundle sealRead pkg ->
                      UnaryHistory banach ∧ UnaryHistory contraction ∧
                        UnaryHistory lipschitz ∧ UnaryHistory iterates ∧
                          UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                            UnaryHistory step ∧ UnaryHistory odeRead ∧
                              UnaryHistory newtonRead ∧ UnaryHistory sealRead ∧
                                Cont banach contraction lipschitz ∧
                                  Cont iterates modulus endpoint ∧
                                    Cont iterates contraction step ∧
                                      Cont iterates endpoint odeRead ∧
                                        Cont endpoint transport newtonRead ∧
                                          Cont endpoint transport sealRead ∧
                                            PkgSig bundle name pkg ∧
                                              PkgSig bundle step pkg ∧
                                                PkgSig bundle odeRead pkg ∧
                                                  PkgSig bundle newtonRead pkg ∧
                                                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesContractionStep iteratesEndpointOdeRead endpointTransportNewtonRead
    endpointTransportSealRead stepPkg odeReadPkg newtonReadPkg sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeRead
  have newtonReadUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewtonRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, stepUnary, odeReadUnary, newtonReadUnary, sealReadUnary,
      banachContractionLipschitz, iteratesModulusEndpoint, iteratesContractionStep,
      iteratesEndpointOdeRead, endpointTransportNewtonRead, endpointTransportSealRead,
      namePkg, stepPkg, odeReadPkg, newtonReadPkg, sealReadPkg⟩

theorem PicardContractionPacket_public_carrier_surface [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      realSeal consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont endpoint transport realSeal ->
        Cont realSeal name consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
              UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
                  UnaryHistory name ∧ UnaryHistory realSeal ∧ UnaryHistory consumer ∧
                    Cont banach contraction lipschitz ∧ Cont iterates modulus endpoint ∧
                      Cont endpoint transport realSeal ∧ Cont realSeal name consumer ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet endpointTransportRealSeal realSealNameConsumer consumerPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, routesUnary, provenanceUnary, nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed endpointUnary transportUnary endpointTransportRealSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed realSealUnary nameUnary realSealNameConsumer
  exact
    ⟨banachUnary,
      contractionUnary,
      lipschitzUnary,
      iteratesUnary,
      modulusUnary,
      endpointUnary,
      transportUnary,
      routesUnary,
      provenanceUnary,
      nameUnary,
      realSealUnary,
      consumerUnary,
      banachContractionLipschitz,
      iteratesModulusEndpoint,
      endpointTransportRealSeal,
      realSealNameConsumer,
      namePkg,
      consumerPkg⟩

theorem PicardContractionPacket_newton_ode_shared_modulus_route [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      odeRead newtonRead sharedModulus : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus sharedModulus ->
        Cont iterates endpoint odeRead ->
          Cont endpoint transport newtonRead ->
            PkgSig bundle sharedModulus pkg ->
              PkgSig bundle odeRead pkg ->
                PkgSig bundle newtonRead pkg ->
                  UnaryHistory modulus ∧ UnaryHistory sharedModulus ∧
                    UnaryHistory odeRead ∧ UnaryHistory newtonRead ∧
                      Cont iterates modulus sharedModulus ∧ Cont iterates endpoint odeRead ∧
                        Cont endpoint transport newtonRead ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle sharedModulus pkg ∧ PkgSig bundle odeRead pkg ∧
                            PkgSig bundle newtonRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet iteratesModulusShared iteratesEndpointOde endpointTransportNewton
    sharedModulusPkg odeReadPkg newtonReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have sharedModulusUnary : UnaryHistory sharedModulus :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusShared
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOde
  have newtonReadUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewton
  exact
    ⟨modulusUnary,
      sharedModulusUnary,
      odeReadUnary,
      newtonReadUnary,
      iteratesModulusShared,
      iteratesEndpointOde,
      endpointTransportNewton,
      namePkg,
      sharedModulusPkg,
      odeReadPkg,
      newtonReadPkg⟩

end BEDC.Derived.PicardContractionUp
