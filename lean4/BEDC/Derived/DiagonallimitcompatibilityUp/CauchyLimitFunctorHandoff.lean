import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.CauchyLimitFunctorUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CauchyLimitFunctorUp

theorem DiagonalLimitCompatibility_cauchy_limit_functor_handoff [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sourceSeal targetSeal transportMap sourceWindow targetWindow functorReadback tolerance
      classifier endpoint hsameRows functorRoutes functorProvenance functorNameCert
      carrierEndpoint terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        functorReadback tolerance classifier endpoint hsameRows functorRoutes functorProvenance
        functorNameCert carrierEndpoint bundle pkg ->
      hsame sourceSeal realSeal ->
      Cont carrierEndpoint realSeal terminal ->
      PkgSig bundle terminal pkg ->
      UnaryHistory realSeal ∧ UnaryHistory carrierEndpoint ∧ UnaryHistory terminal ∧
        hsame sourceSeal realSeal ∧ PkgSig bundle carrierEndpoint pkg ∧
          PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro diagonalCarrier functorCarrier sourceRealSeal carrierTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := diagonalCarrier
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, _sourceWindowUnary,
    _targetWindowUnary, _functorReadbackUnary, _toleranceUnary, _classifierUnary,
    _endpointUnary, _hsameRowsUnary, _functorRoutesUnary, _functorProvenanceUnary,
    _functorNameCertUnary, carrierEndpointUnary, _sourceTransportTarget,
    _sourceTargetReadback, _readbackToleranceClassifier, _classifierEndpointCarrier,
    _hsameRoutesProvenance, carrierEndpointPkg⟩ := functorCarrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed carrierEndpointUnary realSealUnary carrierTerminal
  exact
    ⟨realSealUnary, carrierEndpointUnary, terminalUnary, sourceRealSeal,
      carrierEndpointPkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
