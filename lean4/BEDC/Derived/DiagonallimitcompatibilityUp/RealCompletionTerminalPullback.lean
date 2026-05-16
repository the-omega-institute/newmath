import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRealCompletionTerminalPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      completion branch pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal completion ->
        UnaryHistory branch ->
          Cont completion branch pullback ->
            PkgSig bundle pullback pkg ->
              UnaryHistory diagonal ∧ UnaryHistory triangle ∧ UnaryHistory dyadic ∧
                UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
                  UnaryHistory completion ∧ UnaryHistory branch ∧ UnaryHistory pullback ∧
                    Cont diagonal triangle sealRow ∧ Cont dyadic windows readback ∧
                      Cont readback realSeal completion ∧ Cont completion branch pullback ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier readbackRealSealCompletion branchUnary completionBranchPullback pullbackPkg
  obtain ⟨diagonalUnary, triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealCompletion
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed completionUnary branchUnary completionBranchPullback
  exact
    ⟨diagonalUnary, triangleUnary, dyadicUnary, windowsUnary, readbackUnary, realSealUnary,
      completionUnary, branchUnary, pullbackUnary, diagonalTriangleSeal, dyadicWindowsReadback,
      readbackRealSealCompletion, completionBranchPullback, provenancePkg, pullbackPkg⟩

theorem DiagonalLimitCompatibilityCarrier_real_completion_terminal_pullback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      terminal envelopeRoute refinementRoute uniformRoute pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal terminal ->
        Cont terminal route envelopeRoute ->
          Cont terminal transport refinementRoute ->
            Cont terminal cert uniformRoute ->
              Cont envelopeRoute refinementRoute pullback ->
                PkgSig bundle pullback pkg ->
                  UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory terminal ∧
                    UnaryHistory envelopeRoute ∧ UnaryHistory refinementRoute ∧
                      UnaryHistory uniformRoute ∧ UnaryHistory pullback ∧
                        Cont readback realSeal terminal ∧ Cont terminal route envelopeRoute ∧
                          Cont terminal transport refinementRoute ∧
                            Cont terminal cert uniformRoute ∧
                              Cont envelopeRoute refinementRoute pullback ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier readbackRealSealTerminal terminalRouteEnvelopeRoute
    terminalTransportRefinementRoute terminalCertUniformRoute
    envelopeRouteRefinementRoutePullback pullbackPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, transportUnary, routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  have envelopeRouteUnary : UnaryHistory envelopeRoute :=
    unary_cont_closed terminalUnary routeUnary terminalRouteEnvelopeRoute
  have refinementRouteUnary : UnaryHistory refinementRoute :=
    unary_cont_closed terminalUnary transportUnary terminalTransportRefinementRoute
  have uniformRouteUnary : UnaryHistory uniformRoute :=
    unary_cont_closed terminalUnary certUnary terminalCertUniformRoute
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed envelopeRouteUnary refinementRouteUnary envelopeRouteRefinementRoutePullback
  exact
    ⟨readbackUnary, realSealUnary, terminalUnary, envelopeRouteUnary, refinementRouteUnary,
      uniformRouteUnary, pullbackUnary, readbackRealSealTerminal, terminalRouteEnvelopeRoute,
      terminalTransportRefinementRoute, terminalCertUniformRoute,
      envelopeRouteRefinementRoutePullback, provenancePkg, pullbackPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
