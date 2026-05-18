import BEDC.Derived.KernelAcceptanceAuditWitnessUp

namespace BEDC.Derived.KernelAcceptanceAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem KernelAcceptanceAuditWitnessCarrier_marker_consumer_boundary
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      markerRoute queryBoundary : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont queryBoundary name markerRoute →
          SemanticNameCert
            (fun row : BHist =>
              KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery
                replay transport route provenance name ∧ hsame row markerRoute)
            (fun row : BHist =>
              Cont accepted ledger queryBoundary ∧ Cont queryBoundary name markerRoute ∧
                hsame row markerRoute)
            (fun row : BHist =>
              hsame axiomQuery queryBoundary ∧ hsame name accepted ∧ hsame name ledger ∧
                hsame row markerRoute)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryRoute markerRead
  have carrierWitness := carrier
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, _axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro markerRoute
        (And.intro carrierWitness (hsame_refl markerRoute))
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
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨queryRoute, markerRead, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨queryMatchesAxiom, nameAccepted, nameLedger, source.right⟩
  }

theorem KernelAcceptanceAuditWitnessCarrier_public_export
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary ledgeredRoute markerRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont queryBoundary replay ledgeredRoute →
          Cont ledgeredRoute name markerRoute →
            SemanticNameCert (fun row : BHist => hsame row name)
              (fun row : BHist => hsame row accepted ∧ hsame row ledger)
              (fun _row : BHist =>
                hsame axiomQuery queryBoundary ∧ hsame route ledgeredRoute ∧
                  hsame provenance (append ledger replay) ∧
                    Cont ledgeredRoute name markerRoute)
              hsame ∧ hsame name accepted ∧ hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryRoute ledgerRoute markerRead
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  have routeMatchesLedger : hsame route ledgeredRoute :=
    cont_respects_hsame queryMatchesAxiom (hsame_refl replay) axiomReplayRoute ledgerRoute
  have cert :
      SemanticNameCert (fun row : BHist => hsame row name)
          (fun row : BHist => hsame row accepted ∧ hsame row ledger)
          (fun _row : BHist =>
            hsame axiomQuery queryBoundary ∧ hsame route ledgeredRoute ∧
              hsame provenance (append ledger replay) ∧ Cont ledgeredRoute name markerRoute)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro name (hsame_refl name)
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
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro _row source
        exact ⟨hsame_trans source nameAccepted, hsame_trans source nameLedger⟩
      ledger_sound := by
        intro _row _source
        exact ⟨queryMatchesAxiom, routeMatchesLedger, provenanceSame, markerRead⟩
    }
  exact ⟨cert, nameAccepted, nameLedger⟩

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
