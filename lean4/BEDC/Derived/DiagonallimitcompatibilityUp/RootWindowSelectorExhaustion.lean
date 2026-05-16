import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_window_selector_exhaustion [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      rootBudget rootWindow selectorRead terminalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic rootBudget →
        Cont rootBudget windows rootWindow →
          Cont rootWindow readback selectorRead →
            Cont selectorRead realSeal terminalRead →
              PkgSig bundle terminalRead pkg →
                UnaryHistory rootBudget ∧ UnaryHistory rootWindow ∧
                  UnaryHistory selectorRead ∧ UnaryHistory terminalRead ∧
                    Cont diagonal dyadic rootBudget ∧ Cont rootBudget windows rootWindow ∧
                      Cont rootWindow readback selectorRead ∧
                        Cont selectorRead realSeal terminalRead ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminalRead pkg ∧
                              (Cont terminalRead (BHist.e0 hostTail) selectorRead → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicRoot rootWindowsWindow windowReadbackSelector
    selectorRealTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootBudget :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRoot
  have windowUnary : UnaryHistory rootWindow :=
    unary_cont_closed rootUnary windowsUnary rootWindowsWindow
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed windowUnary readbackUnary windowReadbackSelector
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed selectorUnary realSealUnary selectorRealTerminal
  exact
    ⟨rootUnary, windowUnary, selectorUnary, terminalUnary, diagonalDyadicRoot,
      rootWindowsWindow, windowReadbackSelector, selectorRealTerminal, provenancePkg,
      terminalPkg,
      fun backToSelector =>
        cont_mutual_extension_right_tail_absurd.left selectorRealTerminal backToSelector⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
