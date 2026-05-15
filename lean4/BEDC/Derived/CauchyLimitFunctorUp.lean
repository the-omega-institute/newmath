import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyLimitFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyLimitFunctorCarrier [AskSetup] [PackageSetup]
    (sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceSeal ∧ UnaryHistory targetSeal ∧ UnaryHistory transportMap ∧
    UnaryHistory sourceWindow ∧ UnaryHistory targetWindow ∧ UnaryHistory readback ∧
      UnaryHistory tolerance ∧ UnaryHistory classifier ∧ UnaryHistory endpoint ∧
        UnaryHistory hsameRows ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
          UnaryHistory nameCert ∧ UnaryHistory carrierEndpoint ∧
            Cont sourceSeal transportMap targetSeal ∧
              Cont sourceWindow targetWindow readback ∧
                Cont readback tolerance classifier ∧ Cont classifier endpoint carrierEndpoint ∧
                  Cont hsameRows routes provenance ∧ PkgSig bundle carrierEndpoint pkg

theorem CauchyLimitFunctorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow
              targetWindow readback tolerance classifier endpoint hsameRows routes provenance
              nameCert carrierEndpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow
              targetWindow readback tolerance classifier endpoint hsameRows routes provenance
              nameCert carrierEndpoint bundle pkg ∧
            hsame row nameCert)
        (fun row : BHist =>
          CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow
              targetWindow readback tolerance classifier endpoint hsameRows routes provenance
              nameCert carrierEndpoint bundle pkg ∧
            hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig SemanticNameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro carrier (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchyLimitFunctorCarrier_real_completion_consumer_boundary [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint observationRead consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg ->
      Cont sourceWindow targetWindow observationRead ->
        Cont observationRead classifier consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory sourceWindow ∧ UnaryHistory targetWindow ∧
              UnaryHistory observationRead ∧ UnaryHistory classifier ∧ UnaryHistory consumer ∧
                Cont sourceWindow targetWindow observationRead ∧
                  Cont observationRead classifier consumer ∧
                    Cont sourceSeal transportMap targetSeal ∧
                      Cont readback tolerance classifier ∧
                        Cont classifier endpoint carrierEndpoint ∧
                          PkgSig bundle carrierEndpoint pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceTargetObservation observationClassifierConsumer consumerPkg
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, sourceWindowUnary,
    targetWindowUnary, _readbackUnary, _toleranceUnary, classifierUnary, _endpointUnary,
    _hsameRowsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _carrierEndpointUnary,
    sourceTransportTarget, _sourceTargetReadback, readbackToleranceClassifier,
    classifierEndpointCarrier, _hsameRowsRoutesProvenance, carrierEndpointPkg⟩ := carrier
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed sourceWindowUnary targetWindowUnary sourceTargetObservation
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed observationUnary classifierUnary observationClassifierConsumer
  exact
    ⟨sourceWindowUnary, targetWindowUnary, observationUnary, classifierUnary, consumerUnary,
      sourceTargetObservation, observationClassifierConsumer, sourceTransportTarget,
      readbackToleranceClassifier, classifierEndpointCarrier, carrierEndpointPkg, consumerPkg⟩

theorem CauchyLimitFunctorCarrier_public_seal_export [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg ->
      Cont targetSeal endpoint publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory sourceSeal ∧ UnaryHistory targetSeal ∧ UnaryHistory transportMap ∧
            UnaryHistory sourceWindow ∧ UnaryHistory targetWindow ∧ UnaryHistory readback ∧
              UnaryHistory tolerance ∧ UnaryHistory classifier ∧ UnaryHistory endpoint ∧
                UnaryHistory publicRead ∧ Cont sourceSeal transportMap targetSeal ∧
                  Cont sourceWindow targetWindow readback ∧
                    Cont readback tolerance classifier ∧
                      Cont classifier endpoint carrierEndpoint ∧
                        Cont targetSeal endpoint publicRead ∧
                          PkgSig bundle carrierEndpoint pkg ∧
                            PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier targetEndpointPublic publicPkg
  obtain ⟨sourceSealUnary, targetSealUnary, transportMapUnary, sourceWindowUnary,
    targetWindowUnary, readbackUnary, toleranceUnary, classifierUnary, endpointUnary,
    _hsameRowsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _carrierEndpointUnary,
    sourceTransportTarget, sourceTargetReadback, readbackToleranceClassifier,
    classifierEndpointCarrier, _hsameRowsRoutesProvenance, carrierEndpointPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed targetSealUnary endpointUnary targetEndpointPublic
  exact
    ⟨sourceSealUnary, targetSealUnary, transportMapUnary, sourceWindowUnary,
      targetWindowUnary, readbackUnary, toleranceUnary, classifierUnary, endpointUnary,
      publicReadUnary, sourceTransportTarget, sourceTargetReadback, readbackToleranceClassifier,
      classifierEndpointCarrier, targetEndpointPublic, carrierEndpointPkg, publicPkg⟩

theorem CauchyLimitFunctorCarrier_finite_observation_exposure [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint observationRead toleranceRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg ->
      Cont sourceWindow targetWindow observationRead ->
        Cont observationRead tolerance toleranceRead ->
          PkgSig bundle toleranceRead pkg ->
            UnaryHistory sourceWindow ∧ UnaryHistory targetWindow ∧ UnaryHistory readback ∧
              UnaryHistory tolerance ∧ UnaryHistory classifier ∧ UnaryHistory endpoint ∧
                UnaryHistory observationRead ∧ UnaryHistory toleranceRead ∧
                  Cont sourceWindow targetWindow observationRead ∧
                    Cont observationRead tolerance toleranceRead ∧
                      Cont readback tolerance classifier ∧
                        Cont classifier endpoint carrierEndpoint ∧
                          PkgSig bundle carrierEndpoint pkg ∧
                            PkgSig bundle toleranceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sourceTargetObservation observationToleranceRead toleranceReadPkg
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, sourceWindowUnary,
    targetWindowUnary, readbackUnary, toleranceUnary, classifierUnary, endpointUnary,
    _hsameRowsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _carrierEndpointUnary,
    _sourceTransportTarget, _sourceTargetReadback, readbackToleranceClassifier,
    classifierEndpointCarrier, _hsameRowsRoutesProvenance, carrierEndpointPkg⟩ := carrier
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed sourceWindowUnary targetWindowUnary sourceTargetObservation
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed observationUnary toleranceUnary observationToleranceRead
  exact
    ⟨sourceWindowUnary, targetWindowUnary, readbackUnary, toleranceUnary, classifierUnary,
      endpointUnary, observationUnary, toleranceReadUnary, sourceTargetObservation,
      observationToleranceRead, readbackToleranceClassifier, classifierEndpointCarrier,
      carrierEndpointPkg, toleranceReadPkg⟩

theorem CauchyLimitFunctorCarrier_source_target_seal_exposure [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint sourceSealPrime
      transportMapPrime targetSealPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg ->
      hsame sourceSeal sourceSealPrime ->
        hsame transportMap transportMapPrime ->
          Cont sourceSealPrime transportMapPrime targetSealPrime ->
            hsame targetSeal targetSealPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier sameSource sameTransport transportedRoute
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, _sourceWindowUnary,
    _targetWindowUnary, _readbackUnary, _toleranceUnary, _classifierUnary, _endpointUnary,
    _hsameRowsUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _carrierEndpointUnary,
    sourceTransportTarget, _sourceTargetReadback, _readbackToleranceClassifier,
    _classifierEndpointCarrier, _hsameRowsRoutesProvenance, _carrierEndpointPkg⟩ := carrier
  exact cont_respects_hsame sameSource sameTransport sourceTransportTarget transportedRoute

theorem CauchyLimitFunctorCarrier_structural_transport [AskSetup] [PackageSetup]
    {sourceSeal targetSeal transportMap sourceWindow targetWindow readback tolerance classifier
      endpoint hsameRows routes provenance nameCert carrierEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        readback tolerance classifier endpoint hsameRows routes provenance nameCert
        carrierEndpoint bundle pkg →
      PkgSig bundle provenance pkg →
        UnaryHistory hsameRows ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
          UnaryHistory nameCert ∧ Cont hsameRows routes provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle carrierEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier provenancePkg
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, _sourceWindowUnary,
    _targetWindowUnary, _readbackUnary, _toleranceUnary, _classifierUnary,
    _endpointUnary, hsameRowsUnary, routesUnary, provenanceUnary, nameCertUnary,
    _carrierEndpointUnary, _sourceTransportTarget, _sourceTargetReadback,
    _readbackToleranceClassifier, _classifierEndpointCarrier,
    hsameRowsRoutesProvenance, carrierEndpointPkg⟩ := carrier
  exact
    ⟨hsameRowsUnary, routesUnary, provenanceUnary, nameCertUnary,
      hsameRowsRoutesProvenance, provenancePkg, carrierEndpointPkg⟩

end BEDC.Derived.CauchyLimitFunctorUp
