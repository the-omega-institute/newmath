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

theorem DiagonalLimitCompatibility_root_budget_functor_selector_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sourceSeal targetSeal transportMap sourceWindow targetWindow functorReadback tolerance
      classifier endpoint hsameRows functorRoutes functorProvenance functorNameCert
      carrierEndpoint selectorTerminal functorTerminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        functorReadback tolerance classifier endpoint hsameRows functorRoutes functorProvenance
        functorNameCert carrierEndpoint bundle pkg ->
      Cont readback realSeal selectorTerminal ->
        Cont carrierEndpoint realSeal functorTerminal ->
          hsame carrierEndpoint readback ->
            PkgSig bundle selectorTerminal pkg ->
              PkgSig bundle functorTerminal pkg ->
                UnaryHistory readback ∧ UnaryHistory carrierEndpoint ∧
                  UnaryHistory selectorTerminal ∧ UnaryHistory functorTerminal ∧
                    hsame selectorTerminal functorTerminal ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle carrierEndpoint pkg ∧
                        PkgSig bundle selectorTerminal pkg ∧
                          PkgSig bundle functorTerminal pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig
  intro diagonalCarrier functorCarrier readbackRealSealSelectorTerminal
    carrierEndpointRealSealFunctorTerminal sameCarrierEndpointReadback selectorTerminalPkg
    functorTerminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, _sourceWindowUnary,
    _targetWindowUnary, _functorReadbackUnary, _toleranceUnary, _classifierUnary,
    _endpointUnary, _hsameRowsUnary, _functorRoutesUnary, _functorProvenanceUnary,
    _functorNameCertUnary, carrierEndpointUnary, _sourceTransportTarget,
    _sourceTargetReadback, _readbackToleranceClassifier, _classifierEndpointCarrier,
    _hsameRowsRoutesProvenance, carrierEndpointPkg⟩ := functorCarrier
  have selectorTerminalUnary : UnaryHistory selectorTerminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealSelectorTerminal
  have functorTerminalUnary : UnaryHistory functorTerminal :=
    unary_cont_closed carrierEndpointUnary realSealUnary carrierEndpointRealSealFunctorTerminal
  have sameTerminal : hsame selectorTerminal functorTerminal :=
    cont_respects_hsame (hsame_symm sameCarrierEndpointReadback) (hsame_refl realSeal)
      readbackRealSealSelectorTerminal carrierEndpointRealSealFunctorTerminal
  exact
    ⟨readbackUnary, carrierEndpointUnary, selectorTerminalUnary, functorTerminalUnary,
      sameTerminal, provenancePkg, carrierEndpointPkg, selectorTerminalPkg,
      functorTerminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
