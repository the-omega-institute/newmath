import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_finite_prefix_budget_handoff
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      qF bF wF dF terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory qF ->
        UnaryHistory wF ->
          Cont windows qF bF ->
            Cont bF wF dF ->
              Cont dF readback terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory qF ∧
                    UnaryHistory bF ∧ UnaryHistory wF ∧ UnaryHistory dF ∧
                      UnaryHistory terminal ∧ Cont dyadic windows readback ∧
                        Cont windows qF bF ∧ Cont bF wF dF ∧
                          Cont dF readback terminal ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory DiagonalLimitCompatibilityCarrier
  intro carrier qFUnary wFUnary windowsQF bFWF dFReadback terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have bFUnary : UnaryHistory bF :=
    unary_cont_closed windowsUnary qFUnary windowsQF
  have dFUnary : UnaryHistory dF :=
    unary_cont_closed bFUnary wFUnary bFWF
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed dFUnary readbackUnary dFReadback
  exact
    ⟨windowsUnary, readbackUnary, qFUnary, bFUnary, wFUnary, dFUnary, terminalUnary,
      dyadicWindowsReadback, windowsQF, bFWF, dFReadback, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
