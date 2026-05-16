import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilitySelectorBudgetMonotoneCauchyHandoff
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selected monotoneRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector dyadic selected ->
          Cont selected readback monotoneRead ->
            Cont monotoneRead realSeal terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory selector ∧ UnaryHistory selected ∧ UnaryHistory monotoneRead ∧
                  UnaryHistory terminal ∧ Cont diagonal windows selector ∧
                    Cont selector dyadic selected ∧ Cont selected readback monotoneRead ∧
                      Cont monotoneRead realSeal terminal ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsSelector selectorDyadicSelected selectedReadbackMonotone
    monotoneRealTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute, _routeCertTransport,
    provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed selectorUnary dyadicUnary selectorDyadicSelected
  have monotoneReadUnary : UnaryHistory monotoneRead :=
    unary_cont_closed selectedUnary readbackUnary selectedReadbackMonotone
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed monotoneReadUnary realSealUnary monotoneRealTerminal
  exact
    ⟨selectorUnary, selectedUnary, monotoneReadUnary, terminalUnary, diagonalWindowsSelector,
      selectorDyadicSelected, selectedReadbackMonotone, monotoneRealTerminal, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
