import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_window_ledger_pullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector readback terminal →
          PkgSig bundle terminal pkg →
            UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
              UnaryHistory realSeal ∧ UnaryHistory selector ∧ UnaryHistory terminal ∧
                Cont diagonal windows selector ∧ Cont selector readback terminal ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalWindowsSelector selectorReadbackTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackTerminal
  exact
    ⟨windowsUnary, dyadicUnary, readbackUnary, realSealUnary, selectorUnary,
      terminalUnary, diagonalWindowsSelector, selectorReadbackTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
