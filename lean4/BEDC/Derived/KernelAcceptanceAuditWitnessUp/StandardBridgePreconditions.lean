import BEDC.Derived.KernelAcceptanceAuditWitnessUp

namespace BEDC.Derived.KernelAcceptanceAuditWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KernelAcceptanceAuditWitnessCarrier_standard_bridge_preconditions
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary replayRoute bridgeRead : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont axiomQuery replay replayRoute →
          Cont queryBoundary replay bridgeRead →
        SemanticNameCert
            (fun row : BHist =>
              hsame row bridgeRead ∧
                KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery
                  replay transport route provenance name)
            (fun row : BHist =>
              Cont accepted ledger queryBoundary ∧ Cont axiomQuery replay replayRoute ∧
                hsame row bridgeRead)
            (fun row : BHist =>
              hsame row bridgeRead ∧ hsame axiomQuery queryBoundary ∧
                hsame replayRoute route ∧ hsame name ledger)
            hsame ∧
          hsame axiomQuery queryBoundary ∧ hsame replayRoute route := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryRoute replayRead _bridgeRoute
  have carrierWitness := carrier
  obtain ⟨generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    transportSame, provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  have replayMatchesRoute : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row bridgeRead ∧
              KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery
                replay transport route provenance name)
          (fun row : BHist =>
            Cont accepted ledger queryBoundary ∧ Cont axiomQuery replay replayRoute ∧
              hsame row bridgeRead)
          (fun row : BHist =>
            hsame row bridgeRead ∧ hsame axiomQuery queryBoundary ∧
              hsame replayRoute route ∧ hsame name ledger)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro bridgeRead (And.intro (hsame_refl bridgeRead) carrierWitness)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
      }
      pattern_sound := by
        intro _row source
        exact ⟨queryRoute, replayRead, source.left⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, queryMatchesAxiom, replayMatchesRoute, nameLedger⟩
    }
  exact ⟨cert, queryMatchesAxiom, replayMatchesRoute⟩

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
