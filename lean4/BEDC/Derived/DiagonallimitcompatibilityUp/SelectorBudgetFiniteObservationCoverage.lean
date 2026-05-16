import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FiniteObservationBudgetSelectorUp

theorem DiagonalLimitCompatibilityCarrier_selector_budget_finite_observation_coverage
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budget source selectedWindow selectedDyadic selectedRead selectedSeal selectedTransport
      selectedRoute selectedProvenance selectedName terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      FiniteObservationBudgetSelectorCarrier budget source selectedWindow selectedDyadic
        selectedRead selectedSeal selectedTransport selectedRoute selectedProvenance
        selectedName ->
      hsame selectedWindow windows ->
      hsame selectedDyadic dyadic ->
      hsame selectedRead readback ->
      hsame selectedSeal realSeal ->
      Cont readback realSeal terminal ->
      PkgSig bundle terminal pkg ->
        UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
          UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory budget ∧
            UnaryHistory source ∧ UnaryHistory selectedWindow ∧ UnaryHistory selectedDyadic ∧
              UnaryHistory selectedRead ∧ UnaryHistory selectedSeal ∧ UnaryHistory terminal ∧
                hsame selectedWindow windows ∧ hsame selectedDyadic dyadic ∧
                  hsame selectedRead readback ∧ hsame selectedSeal realSeal ∧
                    Cont readback realSeal terminal ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro compatibilityCarrier selectorCarrier sameWindow sameDyadic sameRead sameSeal
    readbackRealSealTerminal terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := compatibilityCarrier
  obtain ⟨budgetUnary, sourceUnary, selectedDyadicUnary, selectedSealUnary,
    _selectedTransportUnary, budgetSourceWindow, windowDyadicRead,
    _readSealRoute, _nameSealSame⟩ := selectorCarrier
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed budgetUnary sourceUnary budgetSourceWindow
  have selectedReadUnary : UnaryHistory selectedRead :=
    unary_cont_closed selectedWindowUnary selectedDyadicUnary windowDyadicRead
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  exact
    ⟨diagonalUnary, windowsUnary, dyadicUnary, readbackUnary, realSealUnary, budgetUnary,
      sourceUnary, selectedWindowUnary, selectedDyadicUnary, selectedReadUnary,
      selectedSealUnary, terminalUnary, sameWindow, sameDyadic, sameRead, sameSeal,
      readbackRealSealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
