import BEDC.Derived.KernelAcceptanceAuditWitnessUp

namespace BEDC.Derived.KernelAcceptanceAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem KernelAcceptanceAuditWitnessCarrier_public_bridge_boundary
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary replayRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name ->
      Cont accepted ledger queryBoundary ->
        Cont axiomQuery replay replayRoute ->
          SemanticNameCert (fun row : BHist => hsame row name)
            (fun row : BHist => hsame row accepted ∧ hsame row ledger)
            (fun _row : BHist =>
              hsame axiomQuery queryBoundary ∧ hsame replayRoute route ∧
                hsame provenance (append ledger replay) ∧ hsame name accepted ∧
                  hsame name ledger)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryRoute replayRead
  have dependencyCert :=
    KernelAcceptanceAuditWitnessCarrier_dependency_query_exhaustion carrier queryRoute
  obtain
    ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute, _transportSame,
      provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  have replayMatchesRoute : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  have _dependencyWitness := dependencyCert
  exact {
    core := {
      carrier_inhabited := Exists.intro name (hsame_refl name)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact ⟨hsame_trans source nameAccepted, hsame_trans source nameLedger⟩
    ledger_sound := by
      intro _row _source
      exact ⟨queryMatchesAxiom, replayMatchesRoute, provenanceSame, nameAccepted, nameLedger⟩
  }

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
