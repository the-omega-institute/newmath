import BEDC.Derived.KernelAcceptanceAuditWitnessUp

namespace BEDC.Derived.KernelAcceptanceAuditWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem KernelAcceptanceAuditWitnessCarrier_standard_bridge_preconditions
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      bridgeRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name ->
      Cont route name bridgeRoute ->
        SemanticNameCert
          (fun row : BHist =>
            KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery
                replay transport route provenance name ∧
              hsame row bridgeRoute)
          (fun row : BHist =>
            Cont generated candidate accepted ∧ Cont accepted ledger axiomQuery ∧
              Cont axiomQuery replay route ∧ Cont route name row)
          (fun row : BHist =>
            hsame transport (append generated candidate) ∧ hsame provenance (append ledger replay) ∧
              hsame name accepted ∧ hsame name ledger ∧ hsame row bridgeRoute)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier bridgeRead
  have carrierWitness :
      KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name :=
    carrier
  obtain ⟨generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    transportSame, provenanceSame, nameAccepted, nameLedger⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRoute (And.intro carrierWitness (hsame_refl bridgeRoute))
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
      intro row source
      exact
        ⟨generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
          cont_result_hsame_transport bridgeRead (hsame_symm source.right)⟩
    ledger_sound := by
      intro row source
      exact
        ⟨transportSame, provenanceSame, nameAccepted, nameLedger, source.right⟩
  }

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
