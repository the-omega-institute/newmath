import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyTailSelectorCarrier [AskSetup] [PackageSetup]
    (precision stream regularity dyadic realSeal tailWitness transports routes provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory stream ∧ UnaryHistory regularity ∧
    UnaryHistory dyadic ∧ UnaryHistory realSeal ∧ UnaryHistory transports ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont regularity dyadic tailWitness ∧ Cont tailWitness routes provenance ∧
          Cont realSeal provenance localCert ∧ PkgSig bundle provenance pkg

theorem RegularCauchyTailSelectorCarrier_precision_window_exactness [AskSetup]
    [PackageSetup]
    {precision stream regularity dyadic realSeal tailWitness transports routes provenance
      localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailSelectorCarrier precision stream regularity dyadic realSeal tailWitness
        transports routes provenance localCert bundle pkg ->
      Cont tailWitness routes consumer ->
        UnaryHistory precision ∧ UnaryHistory tailWitness ∧ UnaryHistory consumer ∧
          Cont regularity dyadic tailWitness ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerRoute
  obtain ⟨precisionUnary, _streamUnary, regularityUnary, dyadicUnary, _realSealUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, tailWitnessRoute,
    _provenanceRoute, _localCertRoute, pkgSig⟩ := carrier
  have tailWitnessUnary : UnaryHistory tailWitness :=
    unary_cont_closed regularityUnary dyadicUnary tailWitnessRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tailWitnessUnary routesUnary consumerRoute
  exact ⟨precisionUnary, tailWitnessUnary, consumerUnary, tailWitnessRoute, pkgSig⟩

def RegularCauchyTailSelectorPacket [AskSetup] [PackageSetup]
    (precision stream regularity dyadic «seal» witness transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory stream ∧ UnaryHistory regularity ∧
    UnaryHistory dyadic ∧ UnaryHistory «seal» ∧ UnaryHistory witness ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont stream regularity witness ∧ Cont witness dyadic «seal» ∧
          Cont «seal» transport routes ∧ Cont routes provenance name ∧ PkgSig bundle name pkg

theorem RegularCauchyTailSelectorPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision stream regularity dyadic «seal» witness transport routes provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailSelectorPacket precision stream regularity dyadic «seal» witness transport
        routes provenance name bundle pkg ->
      Cont witness regularity consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory precision ∧ UnaryHistory stream ∧ UnaryHistory regularity ∧
            UnaryHistory dyadic ∧ UnaryHistory «seal» ∧ UnaryHistory witness ∧
              UnaryHistory consumer ∧ Cont stream regularity witness ∧
                Cont witness dyadic «seal» ∧ Cont witness regularity consumer ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet witnessRegularityConsumer consumerPkg
  obtain ⟨precisionUnary, streamUnary, regularityUnary, dyadicUnary, sealUnary, witnessUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameUnary, streamRegularityWitness,
    witnessDyadicSeal, _sealTransportRoutes, _routesProvenanceName, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed witnessUnary regularityUnary witnessRegularityConsumer
  exact
    ⟨precisionUnary, streamUnary, regularityUnary, dyadicUnary, sealUnary, witnessUnary,
      consumerUnary, streamRegularityWitness, witnessDyadicSeal, witnessRegularityConsumer,
      namePkg, consumerPkg⟩

theorem RegularCauchyTailSelectorPacket_precision_window_exactness [AskSetup] [PackageSetup]
    {precision stream regularity dyadic «seal» witness transport routes provenance name
      witnessPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailSelectorPacket precision stream regularity dyadic «seal» witness transport
        routes provenance name bundle pkg ->
      Cont stream regularity witnessPrime ->
        UnaryHistory witnessPrime ∧ hsame witness witnessPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet streamRegularityWitnessPrime
  obtain ⟨_precisionUnary, streamUnary, regularityUnary, _dyadicUnary, _sealUnary,
    _witnessUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    streamRegularityWitness, _witnessDyadicSeal, _sealTransportRoutes, _routesProvenanceName,
    _namePkg⟩ := packet
  have witnessPrimeUnary : UnaryHistory witnessPrime :=
    unary_cont_closed streamUnary regularityUnary streamRegularityWitnessPrime
  have sameWitness : hsame witness witnessPrime :=
    cont_respects_hsame (hsame_refl stream) (hsame_refl regularity) streamRegularityWitness
      streamRegularityWitnessPrime
  exact ⟨witnessPrimeUnary, sameWitness⟩

theorem RegularCauchyTailSelectorPacket_classifier_transport [AskSetup] [PackageSetup]
    {precision stream regularity dyadic sealRow witnessRow transport routes provenance name
      precision' stream' regularity' dyadic' sealRow' witnessRow' transport' routes' provenance'
      name' consumer consumer' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    RegularCauchyTailSelectorPacket precision stream regularity dyadic sealRow witnessRow
        transport routes provenance name bundle pkg ->
      RegularCauchyTailSelectorPacket precision' stream' regularity' dyadic' sealRow'
          witnessRow' transport' routes' provenance' name' bundle' pkg' ->
        Cont witnessRow regularity consumer ->
          Cont witnessRow' regularity' consumer' ->
            hsame witnessRow witnessRow' ->
              hsame regularity regularity' ->
                UnaryHistory consumer ∧ UnaryHistory consumer' ∧ hsame consumer consumer' ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle' name' pkg' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet packet' witnessRegularityConsumer witnessRegularityConsumer' sameWitness
    sameRegularity
  obtain ⟨_precisionUnary, _streamUnary, regularityUnary, _dyadicUnary, _sealUnary,
    witnessUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _streamRegularityWitness, _witnessDyadicSeal, _sealTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  obtain ⟨_precisionUnary', _streamUnary', regularityUnary', _dyadicUnary', _sealUnary',
    witnessUnary', _transportUnary', _routesUnary', _provenanceUnary', _nameUnary',
    _streamRegularityWitness', _witnessDyadicSeal', _sealTransportRoutes',
    _routesProvenanceName', namePkg'⟩ := packet'
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed witnessUnary regularityUnary witnessRegularityConsumer
  have consumerUnary' : UnaryHistory consumer' :=
    unary_cont_closed witnessUnary' regularityUnary' witnessRegularityConsumer'
  have sameConsumer : hsame consumer consumer' :=
    cont_respects_hsame sameWitness sameRegularity witnessRegularityConsumer
      witnessRegularityConsumer'
  exact ⟨consumerUnary, consumerUnary', sameConsumer, namePkg, namePkg'⟩

end BEDC.Derived.RegularCauchyTailSelectorUp
