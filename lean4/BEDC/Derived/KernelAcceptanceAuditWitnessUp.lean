import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.KernelAcceptanceAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def KernelAcceptanceAuditWitnessCarrier
    (generated candidate accepted ledger axiomQuery replay transport route provenance
      name : BHist) : Prop :=
  Cont generated candidate accepted ∧
    Cont accepted ledger axiomQuery ∧
      Cont axiomQuery replay route ∧
        hsame transport (append generated candidate) ∧
          hsame provenance (append ledger replay) ∧
            hsame name accepted ∧
              hsame name ledger

theorem KernelAcceptanceAuditWitnessCarrier_namecert_obligations
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      accepted' ledger' : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
      transport route provenance name →
      hsame accepted accepted' →
      hsame ledger ledger' →
      SemanticNameCert (fun row : BHist => hsame row name)
        (fun row : BHist => hsame row accepted')
        (fun row : BHist => hsame row ledger') hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier sameAccepted sameLedger
  have acceptedFromRoute : hsame name accepted' := by
    cases carrier with
    | intro generatedCandidateAccepted rest =>
        cases rest with
        | intro acceptedLedgerAxiom rest =>
            cases rest with
            | intro axiomReplayRoute rest =>
                cases rest with
                | intro transportSame rest =>
                    cases rest with
                    | intro provenanceSame nameSame =>
                        cases generatedCandidateAccepted
                        cases acceptedLedgerAxiom
                        cases axiomReplayRoute
                        cases transportSame
                        cases provenanceSame
                        cases sameAccepted
                        exact nameSame.left
  have ledgerFromRoute : hsame name ledger' := by
    cases carrier with
    | intro generatedCandidateAccepted rest =>
        cases rest with
        | intro acceptedLedgerAxiom rest =>
            cases rest with
            | intro axiomReplayRoute rest =>
                cases rest with
                | intro transportSame rest =>
                    cases rest with
                    | intro provenanceSame rest =>
                        cases generatedCandidateAccepted
                        cases acceptedLedgerAxiom
                        cases axiomReplayRoute
                        cases transportSame
                        cases provenanceSame
                        exact hsame_trans rest.right sameLedger
  exact {
    core := {
      carrier_inhabited := Exists.intro name (hsame_refl name)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro row source
      exact hsame_trans source acceptedFromRoute
    ledger_sound := by
      intro row source
      exact hsame_trans source ledgerFromRoute
  }

theorem KernelAcceptanceAuditWitnessCarrier_route_determinacy
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      replayRoute queryRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont generated candidate replayRoute →
        Cont accepted ledger queryRoute →
          hsame accepted replayRoute ∧ hsame axiomQuery queryRoute ∧
            hsame route (append queryRoute replay) ∧ hsame name accepted ∧
              hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier replayRead queryRead
  obtain ⟨generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have acceptedReplayRoute : hsame accepted replayRoute :=
    cont_respects_hsame (hsame_refl generated) (hsame_refl candidate)
      generatedCandidateAccepted replayRead
  have axiomQueryRoute : hsame axiomQuery queryRoute :=
    cont_respects_hsame (hsame_refl accepted) (hsame_refl ledger) acceptedLedgerAxiom
      queryRead
  have routeQueryReplay : hsame route (append queryRoute replay) := by
    cases axiomQueryRoute
    exact axiomReplayRoute
  exact ⟨acceptedReplayRoute, axiomQueryRoute, routeQueryReplay, nameAccepted, nameLedger⟩

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
