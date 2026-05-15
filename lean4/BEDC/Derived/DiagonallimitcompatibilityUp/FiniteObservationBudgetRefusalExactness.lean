import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_finite_observation_budget_refusal_exactness
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector sealBudget sync refused : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector sealRow sealBudget ->
          Cont sealBudget readback sync ->
            Cont sync cert refused ->
              PkgSig bundle refused pkg ->
                UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory selector ∧
                  UnaryHistory sealRow ∧ UnaryHistory sealBudget ∧ UnaryHistory readback ∧
                    UnaryHistory sync ∧ UnaryHistory cert ∧ UnaryHistory refused ∧
                      Cont diagonal windows selector ∧ Cont selector sealRow sealBudget ∧
                        Cont sealBudget readback sync ∧ Cont sync cert refused ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle refused pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier diagonalWindowsSelector selectorSealBudget sealBudgetReadbackSync
    syncCertRefused refusedPkg
  obtain ⟨diagonalUnary, _triangleUnary, sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed selectorUnary sealRowUnary selectorSealBudget
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed sealBudgetUnary readbackUnary sealBudgetReadbackSync
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed syncUnary certUnary syncCertRefused
  exact
    ⟨diagonalUnary, windowsUnary, selectorUnary, sealRowUnary, sealBudgetUnary,
      readbackUnary, syncUnary, certUnary, refusedUnary, diagonalWindowsSelector,
      selectorSealBudget, sealBudgetReadbackSync, syncCertRefused, provenancePkg,
      refusedPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
