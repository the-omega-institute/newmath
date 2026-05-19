import BEDC.Derived.KernelAcceptanceAuditWitnessUp

namespace BEDC.Derived.KernelAcceptanceAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem KernelAcceptanceAuditWitnessCarrier_terminal_row_semantic_certificate
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      terminalRead : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont axiomQuery replay terminalRead →
        SemanticNameCert
          (fun row : BHist =>
            KernelAcceptanceAuditWitnessTerminalRow accepted ledger axiomQuery replay name
              terminalRead ∧ hsame row terminalRead)
          (fun row : BHist => Cont axiomQuery replay row ∧ hsame row terminalRead)
          (fun row : BHist =>
            hsame row terminalRead ∧ hsame name accepted ∧ hsame name ledger)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier terminalRoute
  have carrierWitness := carrier
  obtain ⟨_generatedCandidateAccepted, _acceptedLedgerAxiom, _axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have terminalRow :
      KernelAcceptanceAuditWitnessTerminalRow accepted ledger axiomQuery replay name
        terminalRead :=
    KernelAcceptanceAuditWitnessTerminalRow_boundary carrierWitness terminalRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead (And.intro terminalRow (hsame_refl terminalRead))
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
        ⟨cont_result_hsame_transport terminalRoute (hsame_symm source.right),
          source.right⟩
    ledger_sound := by
      intro row source
      exact ⟨source.right, nameAccepted, nameLedger⟩
  }

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
