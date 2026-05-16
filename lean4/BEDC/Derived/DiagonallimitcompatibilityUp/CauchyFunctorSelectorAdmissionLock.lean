import BEDC.Derived.CauchyLimitFunctorUp
import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CauchyLimitFunctorUp

theorem DiagonalLimitCompatibility_cauchy_functor_selector_admission_lock
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sourceSeal targetSeal transportMap sourceWindow targetWindow functorReadback tolerance
      classifier endpoint hsameRows functorRoutes functorProvenance functorNameCert
      carrierEndpoint selector synchronizer request budget terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        functorReadback tolerance classifier endpoint hsameRows functorRoutes functorProvenance
        functorNameCert carrierEndpoint bundle pkg ->
      hsame sourceSeal realSeal ->
      Cont diagonal windows selector ->
      Cont selector dyadic synchronizer ->
      Cont synchronizer readback request ->
      Cont request realSeal budget ->
      Cont budget cert terminal ->
      PkgSig bundle carrierEndpoint pkg ->
      PkgSig bundle terminal pkg ->
        UnaryHistory selector ∧ UnaryHistory synchronizer ∧ UnaryHistory request ∧
          UnaryHistory budget ∧ UnaryHistory terminal ∧ hsame sourceSeal realSeal ∧
            PkgSig bundle carrierEndpoint pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro diagonalCarrier functorCarrier sourceRealSeal diagonalWindowsSelector
    selectorDyadicSynchronizer synchronizerReadbackRequest requestRealSealBudget budgetCertTerminal
    carrierEndpointPkg terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := diagonalCarrier
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, _sourceWindowUnary,
    _targetWindowUnary, _functorReadbackUnary, _toleranceUnary, _classifierUnary,
    _endpointUnary, _hsameRowsUnary, _functorRoutesUnary, _functorProvenanceUnary,
    _functorNameCertUnary, _carrierEndpointUnary, _sourceTransportTarget,
    _sourceTargetReadback, _readbackToleranceClassifier, _classifierEndpointCarrier,
    _hsameRoutesProvenance, _carrierEndpointPkgFromFunctor⟩ := functorCarrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have synchronizerUnary : UnaryHistory synchronizer :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadicSynchronizer
  have requestUnary : UnaryHistory request :=
    unary_cont_closed synchronizerUnary readbackUnary synchronizerReadbackRequest
  have budgetUnary : UnaryHistory budget :=
    unary_cont_closed requestUnary realSealUnary requestRealSealBudget
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed budgetUnary certUnary budgetCertTerminal
  exact
    ⟨selectorUnary, synchronizerUnary, requestUnary, budgetUnary, terminalUnary,
      sourceRealSeal, carrierEndpointPkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
