import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_terminal_selector_real_seal_pullback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selectedRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows dyadic selector ->
        Cont selector readback selectedRead ->
          Cont selectedRead realSeal terminal ->
            PkgSig bundle terminal pkg ->
              UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory selector ∧
                UnaryHistory readback ∧ UnaryHistory selectedRead ∧ UnaryHistory realSeal ∧
                  UnaryHistory terminal ∧ Cont windows dyadic selector ∧
                    Cont selector readback selectedRead ∧ Cont selectedRead realSeal terminal ∧
                      Cont route cert transport ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowsDyadicSelector selectorReadbackSelected selectedRealSeal terminalPkg
  rcases carrier with
    ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary, readbackUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _certUnary,
      _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
      routeCertTransport, provenancePkg⟩
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed windowsUnary dyadicUnary windowsDyadicSelector
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackSelected
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed selectedReadUnary realSealUnary selectedRealSeal
  exact
    ⟨windowsUnary, dyadicUnary, selectorUnary, readbackUnary, selectedReadUnary,
      realSealUnary, terminalUnary, windowsDyadicSelector, selectorReadbackSelected,
      selectedRealSeal, routeCertTransport, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
