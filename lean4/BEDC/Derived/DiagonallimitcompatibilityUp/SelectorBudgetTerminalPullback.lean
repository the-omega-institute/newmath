import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorBudgetTerminalPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector terminal sealBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector readback terminal →
          Cont dyadic windows sealBudget →
            Cont terminal realSeal route →
              PkgSig bundle terminal pkg →
                PkgSig bundle route pkg →
                  UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                    UnaryHistory selector ∧ UnaryHistory terminal ∧ UnaryHistory realSeal ∧
                      UnaryHistory route ∧ Cont diagonal windows selector ∧
                        Cont selector readback terminal ∧ Cont dyadic windows sealBudget ∧
                          Cont terminal realSeal route ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminal pkg ∧ PkgSig bundle route pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier diagonalWindowsSelector selectorReadbackTerminal dyadicWindowsSealBudget
    terminalRealSealRoute terminalPkg routePkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackTerminal
  have routeUnary : UnaryHistory route :=
    unary_cont_closed terminalUnary realSealUnary terminalRealSealRoute
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, selectorUnary, terminalUnary, realSealUnary,
      routeUnary, diagonalWindowsSelector, selectorReadbackTerminal, dyadicWindowsSealBudget,
      terminalRealSealRoute, provenancePkg, terminalPkg, routePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
