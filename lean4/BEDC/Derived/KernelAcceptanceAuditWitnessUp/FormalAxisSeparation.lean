import BEDC.Derived.KernelAcceptanceAuditWitnessUp

namespace BEDC.Derived.KernelAcceptanceAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem KernelAcceptanceAuditWitnessCarrier_formal_axis_separation
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary replayRoute markerRead : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name ->
      Cont accepted ledger queryBoundary ->
        Cont axiomQuery replay replayRoute ->
          Cont queryBoundary replay markerRead ->
            SemanticNameCert
                  (fun row : BHist =>
                    hsame row markerRead ∧
                      KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger
                        axiomQuery replay transport route provenance name)
                  (fun row : BHist => Cont queryBoundary replay row ∧ hsame row markerRead)
                  (fun row : BHist =>
                    hsame row route ∧ hsame name accepted ∧ hsame name ledger)
                  hsame ∧
              hsame axiomQuery queryBoundary ∧ hsame replayRoute route ∧
                hsame markerRead route ∧ hsame provenance (append ledger replay) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryRoute replayRead markerRoute
  have carrierWitness := carrier
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  have replayMatchesRoute : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  have markerMatchesRoute : hsame markerRead route :=
    cont_respects_hsame (hsame_symm queryMatchesAxiom) (hsame_refl replay)
      markerRoute axiomReplayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row markerRead ∧
              KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger
                axiomQuery replay transport route provenance name)
          (fun row : BHist => Cont queryBoundary replay row ∧ hsame row markerRead)
          (fun row : BHist => hsame row route ∧ hsame name accepted ∧ hsame name ledger)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro markerRead ⟨hsame_refl markerRead, carrierWitness⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro row source
        exact
          ⟨cont_result_hsame_transport markerRoute (hsame_symm source.left),
            source.left⟩
      ledger_sound := by
        intro row source
        exact
          ⟨hsame_trans source.left markerMatchesRoute, nameAccepted, nameLedger⟩
    }
  exact
    ⟨cert, queryMatchesAxiom, replayMatchesRoute, markerMatchesRoute, provenanceSame⟩

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
