import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_open_phase_budget_terminal_cover [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector synchronizer request budget terminal realScope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector dyadic synchronizer ->
          Cont synchronizer readback request ->
            Cont request realSeal budget ->
              Cont budget cert terminal ->
                Cont terminal realSeal realScope ->
                  PkgSig bundle terminal pkg ->
                    PkgSig bundle realScope pkg ->
                      UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                        UnaryHistory realSeal ∧ UnaryHistory selector ∧
                          UnaryHistory synchronizer ∧ UnaryHistory request ∧
                            UnaryHistory budget ∧ UnaryHistory terminal ∧
                              UnaryHistory realScope ∧ Cont diagonal windows selector ∧
                                Cont selector dyadic synchronizer ∧
                                  Cont synchronizer readback request ∧
                                    Cont request realSeal budget ∧ Cont budget cert terminal ∧
                                      Cont terminal realSeal realScope ∧
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle terminal pkg ∧
                                            PkgSig bundle realScope pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsSelector selectorDyadicSynchronizer
    synchronizerReadbackRequest requestRealSealBudget budgetCertTerminal
    terminalRealSealRealScope terminalPkg realScopePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSealRow, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
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
  have realScopeUnary : UnaryHistory realScope :=
    unary_cont_closed terminalUnary realSealUnary terminalRealSealRealScope
  exact
    ⟨dyadicUnary, windowsUnary, readbackUnary, realSealUnary, selectorUnary,
      synchronizerUnary, requestUnary, budgetUnary, terminalUnary, realScopeUnary,
      diagonalWindowsSelector, selectorDyadicSynchronizer, synchronizerReadbackRequest,
      requestRealSealBudget, budgetCertTerminal, terminalRealSealRealScope, provenancePkg,
      terminalPkg, realScopePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
