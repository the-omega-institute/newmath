import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_root_budget_classifier_row [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      diagonal' dyadic' windows' readback' realSeal' budgetRoot budgetWindow budgetRead
      budgetSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      hsame diagonal diagonal' ->
        hsame dyadic dyadic' ->
          hsame windows windows' ->
            hsame readback readback' ->
              hsame realSeal realSeal' ->
                Cont diagonal' dyadic' budgetRoot ->
                  Cont budgetRoot windows' budgetWindow ->
                    Cont budgetWindow readback' budgetRead ->
                      Cont budgetRead realSeal' budgetSeal ->
                        PkgSig bundle budgetSeal pkg ->
                          UnaryHistory diagonal' ∧ UnaryHistory dyadic' ∧
                            UnaryHistory windows' ∧ UnaryHistory readback' ∧
                              UnaryHistory realSeal' ∧ UnaryHistory budgetRoot ∧
                                UnaryHistory budgetWindow ∧ UnaryHistory budgetRead ∧
                                  UnaryHistory budgetSeal ∧
                                    Cont diagonal' dyadic' budgetRoot ∧
                                      Cont budgetRoot windows' budgetWindow ∧
                                        Cont budgetWindow readback' budgetRead ∧
                                          Cont budgetRead realSeal' budgetSeal ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle budgetSeal pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig
  intro carrier sameDiagonal sameDyadic sameWindows sameReadback sameRealSeal
    diagonalDyadicBudgetRoot budgetRootWindowsBudgetWindow budgetWindowReadbackBudgetRead
    budgetReadRealSealBudgetSeal budgetSealPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have diagonalUnary' : UnaryHistory diagonal' :=
    unary_transport diagonalUnary sameDiagonal
  have dyadicUnary' : UnaryHistory dyadic' :=
    unary_transport dyadicUnary sameDyadic
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have realSealUnary' : UnaryHistory realSeal' :=
    unary_transport realSealUnary sameRealSeal
  have budgetRootUnary : UnaryHistory budgetRoot :=
    unary_cont_closed diagonalUnary' dyadicUnary' diagonalDyadicBudgetRoot
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetRootUnary windowsUnary' budgetRootWindowsBudgetWindow
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary' budgetWindowReadbackBudgetRead
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetReadUnary realSealUnary' budgetReadRealSealBudgetSeal
  exact
    ⟨diagonalUnary', dyadicUnary', windowsUnary', readbackUnary', realSealUnary',
      budgetRootUnary, budgetWindowUnary, budgetReadUnary, budgetSealUnary,
      diagonalDyadicBudgetRoot, budgetRootWindowsBudgetWindow,
      budgetWindowReadbackBudgetRead, budgetReadRealSealBudgetSeal, provenancePkg,
      budgetSealPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
