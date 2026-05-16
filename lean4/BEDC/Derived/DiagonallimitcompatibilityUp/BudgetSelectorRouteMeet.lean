import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.Derived.FiniteObservationBudgetSelectorUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityBudgetSelectorRouteMeet [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert B S
      H C P N sharedWindow sharedRead sharedSeal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      FiniteObservationBudgetSelectorCarrier B S sharedWindow dyadic sharedRead realSeal H C P N ->
        hsame sharedWindow windows ->
          hsame sharedRead readback ->
            hsame sharedSeal realSeal ->
              Cont readback realSeal terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
                    UnaryHistory realSeal ∧ UnaryHistory sharedWindow ∧
                      UnaryHistory sharedRead ∧ UnaryHistory terminal ∧
                        hsame sharedWindow windows ∧ hsame sharedRead readback ∧
                          hsame sharedSeal realSeal ∧ Cont readback realSeal terminal ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig UnaryHistory
  intro diagonalCarrier selectorCarrier sharedWindowSame sharedReadSame sharedSealSame
    readbackRealSealTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨_budgetUnary, _sourceUnary, _selectorDyadicUnary, _selectorSealUnary,
    _selectorTransportUnary, _budgetSourceWindow, _windowDyadicRead, _readSealC,
    _endpointSame⟩ := selectorCarrier
  have sharedWindowUnary : UnaryHistory sharedWindow :=
    unary_transport_symm windowsUnary sharedWindowSame
  have sharedReadUnary : UnaryHistory sharedRead :=
    unary_transport_symm readbackUnary sharedReadSame
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealTerminal
  exact
    ⟨windowsUnary, dyadicUnary, readbackUnary, realSealUnary, sharedWindowUnary,
      sharedReadUnary, terminalUnary, sharedWindowSame, sharedReadSame, sharedSealSame,
      readbackRealSealTerminal, provenancePkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
