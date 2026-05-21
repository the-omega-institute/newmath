import BEDC.Derived.RealityConstrainedTruthCertUp

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealityConstrainedTruthCertOpenFitExportBoundary
    {source signature classifier tower stability descent invariant ledger failure name openFit
      changedFailure exportRead : BHist} :
    RealityConstrainedTruthCertCarrier source signature classifier tower stability descent
        invariant ledger failure name ->
      UnaryHistory openFit ->
        Cont failure openFit changedFailure ->
          Cont changedFailure name exportRead ->
            UnaryHistory failure ∧
              UnaryHistory openFit ∧
                UnaryHistory changedFailure ∧
                  UnaryHistory exportRead ∧
                    Cont invariant ledger failure ∧
                      Cont failure openFit changedFailure ∧
                        Cont changedFailure name exportRead ∧
                          Cont ledger failure name := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier openFitUnary failureOpen exportRoute
  obtain ⟨_sourceUnary, _signatureUnary, _towerUnary, _stabilityUnary, invariantUnary,
    ledgerUnary, _sourceRoute, _towerRoute, invariantRoute, ledgerRoute⟩ := carrier
  have failureUnary : UnaryHistory failure :=
    unary_cont_closed invariantUnary ledgerUnary invariantRoute
  have changedFailureUnary : UnaryHistory changedFailure :=
    unary_cont_closed failureUnary openFitUnary failureOpen
  have nameUnary : UnaryHistory name :=
    unary_cont_closed ledgerUnary failureUnary ledgerRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed changedFailureUnary nameUnary exportRoute
  exact
    ⟨failureUnary, openFitUnary, changedFailureUnary, exportReadUnary, invariantRoute,
      failureOpen, exportRoute, ledgerRoute⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
