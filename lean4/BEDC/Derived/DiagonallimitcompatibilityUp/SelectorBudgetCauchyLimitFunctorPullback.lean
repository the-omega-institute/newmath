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

theorem DiagonalLimitCompatibilityCarrier_selector_budget_cauchy_limit_functor_pullback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      request sealBudget tail selector compatibility locked sourceSeal targetSeal transportMap
      sourceWindow targetWindow functorReadback tolerance classifier endpoint hsameRows functorRoutes
      functorProvenance functorNameCert carrierEndpoint selectorTerminal functorTerminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      CauchyLimitFunctorCarrier sourceSeal targetSeal transportMap sourceWindow targetWindow
        functorReadback tolerance classifier endpoint hsameRows functorRoutes functorProvenance
        functorNameCert carrierEndpoint bundle pkg ->
      UnaryHistory request ->
      UnaryHistory tail ->
      UnaryHistory compatibility ->
      Cont sealRow request sealBudget ->
      Cont sealBudget tail selector ->
      Cont selector compatibility locked ->
      Cont locked realSeal selectorTerminal ->
      Cont carrierEndpoint realSeal functorTerminal ->
      hsame carrierEndpoint locked ->
      PkgSig bundle locked pkg ->
      PkgSig bundle selectorTerminal pkg ->
      PkgSig bundle functorTerminal pkg ->
        UnaryHistory locked ∧ UnaryHistory carrierEndpoint ∧ UnaryHistory selectorTerminal ∧
          UnaryHistory functorTerminal ∧ hsame selectorTerminal functorTerminal ∧
            PkgSig bundle locked pkg ∧ PkgSig bundle carrierEndpoint pkg ∧
              PkgSig bundle selectorTerminal pkg ∧ PkgSig bundle functorTerminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro diagonalCarrier functorCarrier requestUnary tailUnary compatibilityUnary
    sealRowRequestSealBudget sealBudgetTailSelector selectorCompatibilityLocked
    lockedRealSealSelectorTerminal carrierEndpointRealSealFunctorTerminal sameCarrierLocked
    lockedPkg selectorTerminalPkg functorTerminalPkg
  rcases diagonalCarrier with
    ⟨_diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, _windowsUnary,
      _readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
      _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
      _routeCertTransport, _provenancePkg⟩
  rcases functorCarrier with
    ⟨_sourceSealUnary, _targetSealUnary, _transportMapUnary, _sourceWindowUnary,
      _targetWindowUnary, _functorReadbackUnary, _toleranceUnary, _classifierUnary,
      _endpointUnary, _hsameRowsUnary, _functorRoutesUnary, _functorProvenanceUnary,
      _functorNameCertUnary, carrierEndpointUnary, _sourceTransportTarget,
      _sourceTargetReadback, _readbackToleranceClassifier, _classifierEndpointCarrier,
      _hsameRoutesProvenance, carrierEndpointPkg⟩
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed sealRowUnary requestUnary sealRowRequestSealBudget
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary compatibilityUnary selectorCompatibilityLocked
  have selectorTerminalUnary : UnaryHistory selectorTerminal :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealSelectorTerminal
  have functorTerminalUnary : UnaryHistory functorTerminal :=
    unary_cont_closed carrierEndpointUnary realSealUnary carrierEndpointRealSealFunctorTerminal
  have sameTerminal : hsame selectorTerminal functorTerminal :=
    cont_respects_hsame (hsame_symm sameCarrierLocked) (hsame_refl realSeal)
      lockedRealSealSelectorTerminal carrierEndpointRealSealFunctorTerminal
  exact
    ⟨lockedUnary, carrierEndpointUnary, selectorTerminalUnary, functorTerminalUnary,
      sameTerminal, lockedPkg, carrierEndpointPkg, selectorTerminalPkg, functorTerminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
