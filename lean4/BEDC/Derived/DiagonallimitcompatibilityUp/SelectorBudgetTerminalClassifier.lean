import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorBudgetTerminalClassifier [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector synchronizer request budget terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector dyadic synchronizer →
          Cont synchronizer readback request →
            Cont request realSeal budget →
              Cont budget cert terminal →
                PkgSig bundle terminal pkg →
                  UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
                    UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory selector ∧
                      UnaryHistory synchronizer ∧ UnaryHistory request ∧ UnaryHistory budget ∧
                        UnaryHistory terminal ∧ Cont diagonal windows selector ∧
                          Cont selector dyadic synchronizer ∧
                            Cont synchronizer readback request ∧
                              Cont request realSeal budget ∧ Cont budget cert terminal ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalWindowsSelector selectorDyadicSynchronizer synchronizerReadbackRequest
    requestRealSealBudget budgetCertTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
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
  exact
    ⟨diagonalUnary, windowsUnary, dyadicUnary, readbackUnary, realSealUnary, selectorUnary,
      synchronizerUnary, requestUnary, budgetUnary, terminalUnary, diagonalWindowsSelector,
      selectorDyadicSynchronizer, synchronizerReadbackRequest, requestRealSealBudget,
      budgetCertTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
