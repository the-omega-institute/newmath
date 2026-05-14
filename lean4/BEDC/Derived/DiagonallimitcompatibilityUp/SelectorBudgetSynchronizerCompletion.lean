import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_synchronizer_completion_route
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked sync completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows selector ->
        Cont selector readback locked ->
          Cont locked realSeal sync ->
            Cont sync cert completion ->
              PkgSig bundle completion pkg ->
                UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                  UnaryHistory realSeal ∧ UnaryHistory selector ∧ UnaryHistory locked ∧
                    UnaryHistory sync ∧ UnaryHistory completion ∧
                      Cont diagonal windows selector ∧ Cont selector readback locked ∧
                        Cont locked realSeal sync ∧ Cont sync cert completion ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealSync
    syncCertCompletion completionPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealSync
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed syncUnary certUnary syncCertCompletion
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, realSealUnary, selectorUnary,
      lockedUnary, syncUnary, completionUnary, diagonalWindowsSelector,
      selectorReadbackLocked, lockedRealSealSync, syncCertCompletion, provenancePkg,
      completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
