import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibility_terminal_readback_determinacy
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector selector' request request' sealBudget sealBudget' tail sync sync' locked
      locked' terminal terminal' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request ->
        UnaryHistory request' ->
          UnaryHistory tail ->
            Cont diagonal windows selector ->
              Cont diagonal windows selector' ->
                hsame selector selector' ->
                  hsame request request' ->
                    Cont selector request sealBudget ->
                      Cont selector' request' sealBudget' ->
                        Cont sealBudget tail sync ->
                          Cont sealBudget' tail sync' ->
                            Cont sync readback locked ->
                              Cont sync' readback locked' ->
                                Cont locked realSeal terminal ->
                                  Cont locked' realSeal terminal' ->
                                    PkgSig bundle terminal pkg ->
                                      PkgSig bundle terminal' pkg ->
                                        hsame sealBudget sealBudget' ∧ hsame sync sync' ∧
                                          hsame locked locked' ∧ hsame terminal terminal' ∧
                                            UnaryHistory terminal ∧ UnaryHistory terminal' ∧
                                              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory
  intro carrier requestUnary requestUnary' tailUnary diagonalWindowsSelector
    diagonalWindowsSelector' sameSelector sameRequest selectorRequestBudget
    selectorRequestBudget' sealBudgetTailSync sealBudgetTailSync' syncReadbackLocked
    syncReadbackLocked' lockedRealSealTerminal lockedRealSealTerminal' terminalPkg
    terminalPkg'
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sameSealBudget : hsame sealBudget sealBudget' :=
    cont_respects_hsame sameSelector sameRequest selectorRequestBudget selectorRequestBudget'
  have sameSync : hsame sync sync' :=
    cont_respects_hsame sameSealBudget (hsame_refl tail) sealBudgetTailSync
      sealBudgetTailSync'
  have sameLocked : hsame locked locked' :=
    cont_respects_hsame sameSync (hsame_refl readback) syncReadbackLocked
      syncReadbackLocked'
  have sameTerminal : hsame terminal terminal' :=
    cont_respects_hsame sameLocked (hsame_refl realSeal) lockedRealSealTerminal
      lockedRealSealTerminal'
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed
      (unary_cont_closed _diagonalUnary _windowsUnary diagonalWindowsSelector)
      requestUnary selectorRequestBudget
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSync
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed syncUnary readbackUnary syncReadbackLocked
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealTerminal
  have sealBudgetUnary' : UnaryHistory sealBudget' :=
    unary_cont_closed
      (unary_cont_closed _diagonalUnary _windowsUnary diagonalWindowsSelector')
      requestUnary' selectorRequestBudget'
  have syncUnary' : UnaryHistory sync' :=
    unary_cont_closed sealBudgetUnary' tailUnary sealBudgetTailSync'
  have lockedUnary' : UnaryHistory locked' :=
    unary_cont_closed syncUnary' readbackUnary syncReadbackLocked'
  have terminalUnary' : UnaryHistory terminal' :=
    unary_cont_closed lockedUnary' realSealUnary lockedRealSealTerminal'
  exact
    ⟨sameSealBudget, sameSync, sameLocked, sameTerminal, terminalUnary, terminalUnary',
      provenancePkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
