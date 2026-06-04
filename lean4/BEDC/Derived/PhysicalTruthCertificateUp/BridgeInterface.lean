import BEDC.Derived.PhysicalTruthCertificateUp.Carrier

namespace BEDC.Derived.PhysicalTruthCertificateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PhysicalTruthCertificateBridgeInterface
    {S F O D I L R H C P N sourceRead observerRead ledgerRead endpoint : BHist} :
    PhysicalTruthCertificateCarrier S F O D I L R H C P N →
      Cont S F sourceRead →
        Cont sourceRead O observerRead →
          Cont L R ledgerRead →
            Cont observerRead ledgerRead endpoint →
              physicalTruthCertificateFields
                  (PhysicalTruthCertificateUp.mk S F O D I L R H C P N) =
                [S, F, O, D, I, L, R, H, C, P, N] ∧
                UnaryHistory sourceRead ∧ UnaryHistory observerRead ∧
                  UnaryHistory ledgerRead ∧ UnaryHistory endpoint ∧
                    Cont S F sourceRead ∧ Cont sourceRead O observerRead ∧
                      Cont L R ledgerRead ∧ Cont observerRead ledgerRead endpoint ∧
                        hsame endpoint endpoint := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier sourceRoute observerRoute ledgerRoute endpointRoute
  obtain ⟨sourceUnary, fitUnary, observerUnary, _descentUnary, _stabilityUnary,
    ledgerUnary, failureUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _carrierFitRoute, _carrierReplayRoute, _carrierNameRoute⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary fitUnary sourceRoute
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed sourceReadUnary observerUnary observerRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary failureUnary ledgerRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed observerReadUnary ledgerReadUnary endpointRoute
  exact
    ⟨rfl, sourceReadUnary, observerReadUnary, ledgerReadUnary, endpointUnary,
      sourceRoute, observerRoute, ledgerRoute, endpointRoute, hsame_refl endpoint⟩

end BEDC.Derived.PhysicalTruthCertificateUp
