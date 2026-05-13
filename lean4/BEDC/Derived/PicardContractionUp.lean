import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PicardContractionPacket [AskSetup] [PackageSetup]
    (banach contraction lipschitz iterates modulus endpoint transport routes provenance name :
      BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
    UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont banach contraction lipschitz ∧
          Cont iterates modulus endpoint ∧ Cont endpoint transport routes ∧
            Cont routes provenance name ∧ PkgSig bundle name pkg

theorem PicardContractionPacket_finite_iterate_closure [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      nextIterates concatenatedIterates concatenatedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      hsame endpoint nextIterates ->
        Cont iterates nextIterates concatenatedIterates ->
          Cont concatenatedIterates modulus concatenatedEndpoint ->
            Cont concatenatedEndpoint transport routes ->
              PicardContractionPacket banach contraction lipschitz concatenatedIterates modulus
                  concatenatedEndpoint transport routes provenance name bundle pkg ∧
                hsame endpoint nextIterates ∧ UnaryHistory concatenatedIterates ∧
                  UnaryHistory concatenatedEndpoint := by
  intro packet sameEndpointNextIterates iteratesNextIteratesConcatenated
    concatenatedIteratesModulusEndpoint concatenatedEndpointTransportRoutes
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, routesUnary, provenanceUnary, nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    routesProvenanceName, namePkg⟩ := packet
  have nextIteratesUnary : UnaryHistory nextIterates :=
    unary_transport endpointUnary sameEndpointNextIterates
  have concatenatedIteratesUnary : UnaryHistory concatenatedIterates :=
    unary_cont_closed iteratesUnary nextIteratesUnary iteratesNextIteratesConcatenated
  have concatenatedEndpointUnary : UnaryHistory concatenatedEndpoint :=
    unary_cont_closed concatenatedIteratesUnary modulusUnary concatenatedIteratesModulusEndpoint
  have closedPacket :
      PicardContractionPacket banach contraction lipschitz concatenatedIterates modulus
          concatenatedEndpoint transport routes provenance name bundle pkg := by
    exact
      ⟨banachUnary, contractionUnary, lipschitzUnary, concatenatedIteratesUnary, modulusUnary,
        concatenatedEndpointUnary, transportUnary, routesUnary, provenanceUnary, nameUnary,
        banachContractionLipschitz, concatenatedIteratesModulusEndpoint,
        concatenatedEndpointTransportRoutes, routesProvenanceName, namePkg⟩
  exact
    ⟨closedPacket, sameEndpointNextIterates, concatenatedIteratesUnary,
      concatenatedEndpointUnary⟩

theorem PicardContractionPacket_banach_ode_boundary [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates endpoint consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
            UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
              UnaryHistory consumer ∧ Cont banach contraction lipschitz ∧
                Cont iterates modulus endpoint ∧ Cont iterates endpoint consumer ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  intro packet iteratesEndpointConsumer consumerPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, consumerUnary, banachContractionLipschitz, iteratesModulusEndpoint,
      iteratesEndpointConsumer, namePkg, consumerPkg⟩

theorem PicardContractionPacket_contraction_step_package [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name step :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates contraction step ->
        PkgSig bundle step pkg ->
          UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory iterates ∧
            UnaryHistory step ∧ Cont banach contraction lipschitz ∧
              Cont iterates contraction step ∧ Cont iterates modulus endpoint ∧
                PkgSig bundle name pkg ∧ PkgSig bundle step pkg := by
  intro packet iteratesContractionStep stepPkg
  obtain ⟨banachUnary, contractionUnary, _lipschitzUnary, iteratesUnary, _modulusUnary,
    _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  exact
    ⟨banachUnary, contractionUnary, iteratesUnary, stepUnary, banachContractionLipschitz,
      iteratesContractionStep, iteratesModulusEndpoint, namePkg, stepPkg⟩

theorem PicardContractionPacket_classifier_stability [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      banach' contraction' iterates' modulus' endpoint' transport' routes' provenance' name'
      lipschitz' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      hsame banach banach' ->
        hsame contraction contraction' ->
          hsame iterates iterates' ->
            hsame modulus modulus' ->
              hsame endpoint endpoint' ->
                hsame transport transport' ->
                  hsame routes routes' ->
                    hsame provenance provenance' ->
                      Cont banach' contraction' lipschitz' ->
                        Cont iterates' modulus' endpoint' ->
                          Cont endpoint' transport' routes' ->
                            Cont routes' provenance' name' ->
                              PkgSig bundle name' pkg ->
                                PicardContractionPacket banach' contraction' lipschitz'
                                    iterates' modulus' endpoint' transport' routes' provenance'
                                    name' bundle pkg ∧
                                  hsame lipschitz lipschitz' ∧ hsame name name' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameBanach sameContraction sameIterates sameModulus sameEndpoint sameTransport
    sameRoutes sameProvenance banachContractionLipschitz' iteratesModulusEndpoint'
    endpointTransportRoutes' routesProvenanceName' namePkg'
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, routesUnary, provenanceUnary, nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, endpointTransportRoutes,
    routesProvenanceName, _namePkg⟩ := packet
  have sameLipschitz : hsame lipschitz lipschitz' :=
    cont_respects_hsame sameBanach sameContraction banachContractionLipschitz
      banachContractionLipschitz'
  have sameName : hsame name name' :=
    cont_respects_hsame sameRoutes sameProvenance routesProvenanceName routesProvenanceName'
  have banachUnary' : UnaryHistory banach' :=
    unary_transport banachUnary sameBanach
  have contractionUnary' : UnaryHistory contraction' :=
    unary_transport contractionUnary sameContraction
  have lipschitzUnary' : UnaryHistory lipschitz' :=
    unary_transport lipschitzUnary sameLipschitz
  have iteratesUnary' : UnaryHistory iterates' :=
    unary_transport iteratesUnary sameIterates
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have transportUnary' : UnaryHistory transport' :=
    unary_transport transportUnary sameTransport
  have routesUnary' : UnaryHistory routes' :=
    unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' :=
    unary_transport nameUnary sameName
  have transported :
      PicardContractionPacket banach' contraction' lipschitz' iterates' modulus' endpoint'
        transport' routes' provenance' name' bundle pkg :=
    ⟨banachUnary', contractionUnary', lipschitzUnary', iteratesUnary', modulusUnary',
      endpointUnary', transportUnary', routesUnary', provenanceUnary', nameUnary',
      banachContractionLipschitz', iteratesModulusEndpoint', endpointTransportRoutes',
      routesProvenanceName', namePkg'⟩
  exact ⟨transported, sameLipschitz, sameName⟩

theorem PicardContractionPacket_ratio_window_carrier_transport [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      iterates' modulus' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      hsame iterates iterates' ->
        hsame modulus modulus' ->
          Cont iterates' modulus' endpoint' ->
            hsame endpoint endpoint' ∧ UnaryHistory modulus' ∧ UnaryHistory endpoint' ∧
              Cont iterates' modulus' endpoint' ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameIterates sameModulus iteratesModulusEndpoint'
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, _iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameIterates sameModulus iteratesModulusEndpoint
      iteratesModulusEndpoint'
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  exact
    ⟨sameEndpoint, modulusUnary', endpointUnary', iteratesModulusEndpoint', namePkg⟩

theorem PicardContractionPacket_modulus_window_transport [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      modulus' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      hsame modulus modulus' ->
        hsame endpoint endpoint' ->
          Cont iterates modulus' endpoint' ->
            Cont endpoint' transport routes ->
              PicardContractionPacket banach contraction lipschitz iterates modulus' endpoint'
                  transport routes provenance name bundle pkg ∧
                UnaryHistory modulus' ∧ UnaryHistory endpoint' ∧ hsame endpoint endpoint' := by
  intro packet sameModulus sameEndpoint iteratesModulusEndpoint' endpointTransportRoutes'
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, routesUnary, provenanceUnary, nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    routesProvenanceName, namePkg⟩ := packet
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have transported :
      PicardContractionPacket banach contraction lipschitz iterates modulus' endpoint'
          transport routes provenance name bundle pkg :=
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary',
      endpointUnary', transportUnary, routesUnary, provenanceUnary, nameUnary,
      banachContractionLipschitz, iteratesModulusEndpoint', endpointTransportRoutes',
      routesProvenanceName, namePkg⟩
  exact ⟨transported, modulusUnary', endpointUnary', sameEndpoint⟩

theorem PicardContractionPacket_banach_ode_consumer_nonescape [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name step
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates contraction step ->
        Cont iterates endpoint consumer ->
          PkgSig bundle step pkg ->
            PkgSig bundle consumer pkg ->
              UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                  UnaryHistory step ∧ UnaryHistory consumer ∧
                    Cont banach contraction lipschitz ∧ Cont iterates contraction step ∧
                      Cont iterates modulus endpoint ∧ Cont iterates endpoint consumer ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle step pkg ∧
                          PkgSig bundle consumer pkg := by
  intro packet iteratesContractionStep iteratesEndpointConsumer stepPkg consumerPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, stepUnary, consumerUnary, banachContractionLipschitz,
      iteratesContractionStep, iteratesModulusEndpoint, iteratesEndpointConsumer, namePkg,
      stepPkg, consumerPkg⟩

theorem PicardContractionPacket_ratio_ledger_nonexpansion [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      nextIterates concatenatedIterates concatenatedEndpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      hsame endpoint nextIterates ->
        Cont iterates nextIterates concatenatedIterates ->
          Cont concatenatedIterates modulus concatenatedEndpoint ->
            Cont concatenatedEndpoint transport routes ->
              Cont concatenatedIterates concatenatedEndpoint consumer ->
                PkgSig bundle consumer pkg ->
                  PicardContractionPacket banach contraction lipschitz concatenatedIterates
                      modulus concatenatedEndpoint transport routes provenance name bundle pkg ∧
                    UnaryHistory lipschitz ∧ UnaryHistory concatenatedIterates ∧
                      UnaryHistory concatenatedEndpoint ∧ UnaryHistory consumer ∧
                        Cont banach contraction lipschitz ∧
                          Cont concatenatedIterates modulus concatenatedEndpoint ∧
                            Cont concatenatedIterates concatenatedEndpoint consumer ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet sameEndpointNextIterates iteratesNextIteratesConcatenated
    concatenatedIteratesModulusEndpoint concatenatedEndpointTransportRoutes
    concatenatedIteratesEndpointConsumer consumerPkg
  obtain ⟨closedPacket, _sameEndpointNextIterates, concatenatedIteratesUnary,
    concatenatedEndpointUnary⟩ :=
    PicardContractionPacket_finite_iterate_closure packet sameEndpointNextIterates
      iteratesNextIteratesConcatenated concatenatedIteratesModulusEndpoint
      concatenatedEndpointTransportRoutes
  obtain ⟨_banachUnary, _contractionUnary, lipschitzUnary, _iteratesUnary, _modulusUnary,
    _endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed concatenatedIteratesUnary concatenatedEndpointUnary
      concatenatedIteratesEndpointConsumer
  exact
    ⟨closedPacket, lipschitzUnary, concatenatedIteratesUnary, concatenatedEndpointUnary,
      consumerUnary, banachContractionLipschitz, concatenatedIteratesModulusEndpoint,
      concatenatedIteratesEndpointConsumer, namePkg, consumerPkg⟩

theorem PicardContractionPacket_cauchyrate_source_extraction [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont rateSource endpoint routes ->
          PkgSig bundle rateSource pkg ->
            UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
              UnaryHistory rateSource ∧ Cont iterates modulus rateSource ∧
                Cont rateSource endpoint routes ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle rateSource pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRateSource rateSourceEndpointRoutes rateSourcePkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  exact
    ⟨iteratesUnary, modulusUnary, endpointUnary, rateSourceUnary,
      iteratesModulusRateSource, rateSourceEndpointRoutes, namePkg, rateSourcePkg⟩

theorem PicardContractionPacket_cauchyrate_real_seal_compatibility [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont rateSource endpoint routes ->
          Cont endpoint transport sealRead ->
            PkgSig bundle rateSource pkg ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory rateSource ∧ UnaryHistory sealRead ∧
                  Cont iterates modulus rateSource ∧ Cont rateSource endpoint routes ∧
                    Cont endpoint transport sealRead ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle rateSource pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRateSource rateSourceEndpointRoutes endpointTransportSealRead
    rateSourcePkg sealReadPkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨rateSourceUnary, sealReadUnary, iteratesModulusRateSource, rateSourceEndpointRoutes,
      endpointTransportSealRead, namePkg, rateSourcePkg, sealReadPkg⟩

theorem PicardContractionPacket_public_namecert_export [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name step
      consumer sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates contraction step ->
        Cont iterates endpoint consumer ->
          Cont endpoint transport sealRead ->
            PkgSig bundle step pkg ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle sealRead pkg ->
                  UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                    UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                      UnaryHistory step ∧ UnaryHistory consumer ∧ UnaryHistory sealRead ∧
                        Cont banach contraction lipschitz ∧ Cont iterates contraction step ∧
                          Cont iterates modulus endpoint ∧ Cont iterates endpoint consumer ∧
                            Cont endpoint transport sealRead ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle step pkg ∧ PkgSig bundle consumer pkg ∧
                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesContractionStep iteratesEndpointConsumer endpointTransportSealRead
    stepPkg consumerPkg sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary, endpointUnary,
      stepUnary, consumerUnary, sealReadUnary, banachContractionLipschitz,
      iteratesContractionStep, iteratesModulusEndpoint, iteratesEndpointConsumer,
      endpointTransportSealRead, namePkg, stepPkg, consumerPkg, sealReadPkg⟩

theorem PicardContractionPacket_public_banach_cauchyrate_factorization
    [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource banachRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont banach rateSource banachRead ->
          PkgSig bundle rateSource pkg ->
            PkgSig bundle banachRead pkg ->
              UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                  UnaryHistory rateSource ∧ UnaryHistory banachRead ∧
                    Cont banach contraction lipschitz ∧ Cont iterates modulus rateSource ∧
                      Cont banach rateSource banachRead ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle rateSource pkg ∧ PkgSig bundle banachRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRateSource banachRateSourceRead rateSourcePkg banachReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have banachReadUnary : UnaryHistory banachRead :=
    unary_cont_closed banachUnary rateSourceUnary banachRateSourceRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, rateSourceUnary, banachReadUnary, banachContractionLipschitz,
      iteratesModulusRateSource, banachRateSourceRead, namePkg, rateSourcePkg,
      banachReadPkg⟩

theorem PicardContractionPacket_finite_modulus_obligation_triad [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont endpoint transport sealRead ->
        PkgSig bundle sealRead pkg ->
          UnaryHistory banach /\ UnaryHistory lipschitz /\ UnaryHistory modulus /\
            UnaryHistory sealRead /\ Cont banach contraction lipschitz /\
              Cont iterates modulus endpoint /\ Cont endpoint transport sealRead /\
                PkgSig bundle name pkg /\ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet endpointTransportSealRead sealReadPkg
  obtain ⟨banachUnary, _contractionUnary, lipschitzUnary, _iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, lipschitzUnary, modulusUnary, sealReadUnary, banachContractionLipschitz,
      iteratesModulusEndpoint, endpointTransportSealRead, namePkg, sealReadPkg⟩

theorem PicardContractionPacket_public_ode_newton_export [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      odeRead newtonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates endpoint odeRead ->
        Cont endpoint transport newtonRead ->
          PkgSig bundle odeRead pkg ->
            PkgSig bundle newtonRead pkg ->
              UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                  UnaryHistory odeRead ∧ UnaryHistory newtonRead ∧
                    Cont banach contraction lipschitz ∧ Cont iterates modulus endpoint ∧
                      Cont iterates endpoint odeRead ∧ Cont endpoint transport newtonRead ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle odeRead pkg ∧
                          PkgSig bundle newtonRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesEndpointOdeRead endpointTransportNewtonRead odeReadPkg newtonReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have odeReadUnary : UnaryHistory odeRead :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointOdeRead
  have newtonReadUnary : UnaryHistory newtonRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportNewtonRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, odeReadUnary, newtonReadUnary, banachContractionLipschitz,
      iteratesModulusEndpoint, iteratesEndpointOdeRead, endpointTransportNewtonRead,
      namePkg, odeReadPkg, newtonReadPkg⟩

theorem PicardContractionPacket_public_real_consumer_boundary [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      rateSource step consumer sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      Cont iterates modulus rateSource ->
        Cont rateSource endpoint routes ->
          Cont iterates contraction step ->
            Cont iterates endpoint consumer ->
              Cont endpoint transport sealRead ->
                PkgSig bundle rateSource pkg ->
                  PkgSig bundle step pkg ->
                    PkgSig bundle consumer pkg ->
                      PkgSig bundle sealRead pkg ->
                        UnaryHistory banach ∧ UnaryHistory contraction ∧
                          UnaryHistory lipschitz ∧ UnaryHistory iterates ∧
                            UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                              UnaryHistory rateSource ∧ UnaryHistory step ∧
                                UnaryHistory consumer ∧ UnaryHistory sealRead ∧
                                  Cont banach contraction lipschitz ∧
                                    Cont iterates modulus rateSource ∧
                                      Cont rateSource endpoint routes ∧
                                        Cont iterates contraction step ∧
                                          Cont iterates endpoint consumer ∧
                                            Cont endpoint transport sealRead ∧
                                              PkgSig bundle name pkg ∧
                                                PkgSig bundle rateSource pkg ∧
                                                  PkgSig bundle step pkg ∧
                                                    PkgSig bundle consumer pkg ∧
                                                      PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet iteratesModulusRateSource rateSourceEndpointRoutes iteratesContractionStep
    iteratesEndpointConsumer endpointTransportSealRead rateSourcePkg stepPkg consumerPkg
    sealReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have rateSourceUnary : UnaryHistory rateSource :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusRateSource
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary, endpointUnary,
      rateSourceUnary, stepUnary, consumerUnary, sealReadUnary, banachContractionLipschitz,
      iteratesModulusRateSource, rateSourceEndpointRoutes, iteratesContractionStep,
      iteratesEndpointConsumer, endpointTransportSealRead, namePkg, rateSourcePkg, stepPkg,
      consumerPkg, sealReadPkg⟩

def PicardContractionRootSourceWindowPacket [AskSetup] [PackageSetup]
    (banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      request : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
      routes provenance name bundle pkg ∧
    UnaryHistory request

theorem PicardContractionRootSourceWindowPacket_admission [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      request step consumer sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionRootSourceWindowPacket banach contraction lipschitz iterates modulus
        endpoint transport routes provenance name request bundle pkg ->
      Cont iterates contraction step ->
        Cont iterates endpoint consumer ->
          Cont endpoint transport sealRead ->
            PkgSig bundle step pkg ->
              PkgSig bundle consumer pkg ->
                PkgSig bundle sealRead pkg ->
                  PicardContractionRootSourceWindowPacket banach contraction lipschitz
                      iterates modulus endpoint transport routes provenance name request
                      bundle pkg ∧
                    UnaryHistory step ∧ UnaryHistory consumer ∧ UnaryHistory sealRead ∧
                      Cont banach contraction lipschitz ∧ Cont iterates modulus endpoint ∧
                        Cont iterates contraction step ∧ Cont iterates endpoint consumer ∧
                          Cont endpoint transport sealRead ∧ PkgSig bundle name pkg ∧
                            PkgSig bundle step pkg ∧ PkgSig bundle consumer pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro rootPacket iteratesContractionStep iteratesEndpointConsumer endpointTransportSealRead
    stepPkg consumerPkg sealReadPkg
  have closedRoot :
      PicardContractionRootSourceWindowPacket banach contraction lipschitz iterates modulus
          endpoint transport routes provenance name request bundle pkg :=
    rootPacket
  obtain ⟨picardPacket, _requestUnary⟩ := rootPacket
  obtain ⟨_banachUnary, contractionUnary, _lipschitzUnary, iteratesUnary, _modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := picardPacket
  have stepUnary : UnaryHistory step :=
    unary_cont_closed iteratesUnary contractionUnary iteratesContractionStep
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed iteratesUnary endpointUnary iteratesEndpointConsumer
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  exact
    ⟨closedRoot, stepUnary, consumerUnary, sealReadUnary, banachContractionLipschitz,
      iteratesModulusEndpoint, iteratesContractionStep, iteratesEndpointConsumer,
      endpointTransportSealRead, namePkg, stepPkg, consumerPkg, sealReadPkg⟩

end BEDC.Derived.PicardContractionUp
