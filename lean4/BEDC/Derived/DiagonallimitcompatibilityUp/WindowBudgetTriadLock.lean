import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_window_budget_triad_lock [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      triad terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows triad ->
        Cont triad readback terminal ->
          PkgSig bundle terminal pkg ->
            UnaryHistory dyadic ∧ UnaryHistory windows ∧ UnaryHistory triad ∧
              UnaryHistory readback ∧ UnaryHistory terminal ∧ Cont dyadic windows triad ∧
                Cont triad readback terminal ∧ Cont readback realSeal route ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory DiagonalLimitCompatibilityCarrier
  intro carrier dyadicWindowsTriad triadReadbackTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have triadUnary : UnaryHistory triad :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsTriad
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed triadUnary readbackUnary triadReadbackTerminal
  exact
    ⟨dyadicUnary, windowsUnary, triadUnary, readbackUnary, terminalUnary,
      dyadicWindowsTriad, triadReadbackTerminal, readbackRealSealRoute, provenancePkg,
      terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
