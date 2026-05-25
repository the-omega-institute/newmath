import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.Derived.KernelAcceptanceWitnessUp

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

theorem KernelAcceptanceAuditWitnessCarrier_acceptance_witness_alignment_consumer
    {generated candidate accepted ledger axiomQuery replay transport route provenance
      name : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      (∀ h : BHist,
        BEDC.Derived.KernelAcceptanceWitnessUp.kernelAcceptanceWitnessDecodeBHist
            (BEDC.Derived.KernelAcceptanceWitnessUp.kernelAcceptanceWitnessEncodeBHist h) =
          h) ∧
        (∀ x : BEDC.Derived.KernelAcceptanceWitnessUp.KernelAcceptanceWitnessUp,
          BEDC.Derived.KernelAcceptanceWitnessUp.kernelAcceptanceWitnessFromEventFlow
              (BEDC.Derived.KernelAcceptanceWitnessUp.kernelAcceptanceWitnessToEventFlow x) =
            some x) ∧
          (∀ x y : BEDC.Derived.KernelAcceptanceWitnessUp.KernelAcceptanceWitnessUp,
            BEDC.Derived.KernelAcceptanceWitnessUp.kernelAcceptanceWitnessToEventFlow x =
                BEDC.Derived.KernelAcceptanceWitnessUp.kernelAcceptanceWitnessToEventFlow y →
              x = y) ∧
            Cont generated candidate accepted ∧ Cont accepted ledger axiomQuery ∧
              hsame name accepted ∧ hsame name ledger ∧
                BEDC.Derived.KernelAcceptanceWitnessUp.kernelAcceptanceWitnessEncodeBHist
                  BHist.Empty = ([] : List BEDC.FKernel.Mark.BMark) := by
  -- BEDC touchpoint anchor: BHist Cont hsame KernelAcceptanceWitnessUp
  intro carrier
  have alignment :=
    BEDC.Derived.KernelAcceptanceWitnessUp.KernelAcceptanceWitnessTasteGate_single_carrier_alignment
  obtain ⟨decodeEncode, roundTrip, injective, emptyEncode⟩ := alignment
  obtain ⟨generatedCandidateAccepted, acceptedLedgerAxiom, _axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  exact
    ⟨decodeEncode, roundTrip, injective, generatedCandidateAccepted, acceptedLedgerAxiom,
      nameAccepted, nameLedger, emptyEncode⟩

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

theorem KernelAcceptanceAuditWitnessCarrier_source_gate
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      acceptedRoute ledgerRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont generated candidate acceptedRoute →
        Cont acceptedRoute ledger ledgerRoute →
          hsame accepted acceptedRoute ∧ hsame axiomQuery ledgerRoute ∧
            hsame name accepted ∧ hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier sourceRoute ledgerRouteRead
  obtain ⟨generatedCandidateAccepted, acceptedLedgerAxiom, _axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have acceptedMatchesRoute : hsame accepted acceptedRoute :=
    cont_respects_hsame (hsame_refl generated) (hsame_refl candidate)
      generatedCandidateAccepted sourceRoute
  have queryMatchesLedgerRoute : hsame axiomQuery ledgerRoute :=
    cont_respects_hsame acceptedMatchesRoute (hsame_refl ledger) acceptedLedgerAxiom
      ledgerRouteRead
  exact ⟨acceptedMatchesRoute, queryMatchesLedgerRoute, nameAccepted, nameLedger⟩

theorem KernelAcceptanceAuditWitnessCarrier_build_replay_coverage
    {generated candidate accepted ledger axiomQuery replay transport route provenance name replayRoute
      routePrime : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont axiomQuery replay replayRoute →
        Cont axiomQuery replay routePrime →
          hsame route routePrime ∧ hsame replayRoute routePrime ∧ hsame name accepted ∧
            hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier replayRead routeRead
  obtain ⟨_generatedCandidateAccepted, _acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have routeCovered : hsame route routePrime :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) axiomReplayRoute
      routeRead
  have replayCovered : hsame replayRoute routePrime :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead routeRead
  exact ⟨routeCovered, replayCovered, nameAccepted, nameLedger⟩

theorem KernelAcceptanceAuditWitnessCarrier_bridge_query_replay_boundary
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      replayRoute queryRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont axiomQuery replay replayRoute →
        Cont accepted ledger queryRoute →
          hsame replayRoute route ∧ hsame axiomQuery queryRoute ∧ hsame name accepted ∧
            hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier replayRead queryRead
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have replayRouteMatchesCarrier : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  have queryRouteMatchesAxiom : hsame axiomQuery queryRoute :=
    cont_respects_hsame (hsame_refl accepted) (hsame_refl ledger) acceptedLedgerAxiom
      queryRead
  exact
    ⟨replayRouteMatchesCarrier, queryRouteMatchesAxiom, nameAccepted, nameLedger⟩

theorem KernelAcceptanceAuditWitnessCarrier_query_replay_interface
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      replayRoute queryRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont axiomQuery replay replayRoute →
        Cont accepted ledger queryRoute →
          hsame replayRoute route ∧ hsame axiomQuery queryRoute ∧ hsame name accepted ∧
            hsame name ledger ∧ hsame route (append queryRoute replay) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier replayRead queryRead
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have replayRouteMatchesCarrier : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  have queryRouteMatchesAxiom : hsame axiomQuery queryRoute :=
    cont_respects_hsame (hsame_refl accepted) (hsame_refl ledger) acceptedLedgerAxiom
      queryRead
  have carrierRouteFromQuery : hsame route (append queryRoute replay) := by
    cases queryRouteMatchesAxiom
    exact axiomReplayRoute
  exact
    ⟨replayRouteMatchesCarrier, queryRouteMatchesAxiom, nameAccepted, nameLedger,
      carrierRouteFromQuery⟩

theorem KernelAcceptanceAuditWitnessCarrier_dependency_query_exhaustion
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        SemanticNameCert (fun row : BHist => hsame row name)
          (fun row : BHist => hsame row accepted ∧ hsame row ledger)
          (fun _row : BHist =>
            Cont accepted ledger axiomQuery ∧ Cont accepted ledger queryBoundary ∧
              hsame axiomQuery queryBoundary)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryBoundaryRoute
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, _axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryBoundaryRoute
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
      exact ⟨acceptedLedgerAxiom, queryBoundaryRoute, queryMatchesAxiom⟩
  }

theorem KernelAcceptanceAuditWitnessCarrier_query_ledger_totality
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary ledgeredRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont queryBoundary replay ledgeredRoute →
          hsame axiomQuery queryBoundary ∧ hsame route ledgeredRoute ∧
            hsame name accepted ∧ hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier queryRoute ledgerRoute
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  have routeMatchesLedger : hsame route ledgeredRoute :=
    cont_respects_hsame queryMatchesAxiom (hsame_refl replay) axiomReplayRoute ledgerRoute
  exact ⟨queryMatchesAxiom, routeMatchesLedger, nameAccepted, nameLedger⟩

theorem KernelAcceptanceAuditWitnessCarrier_accepted_row_consumer_boundary
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary ledgeredRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont queryBoundary replay ledgeredRoute →
          hsame axiomQuery queryBoundary ∧ hsame route ledgeredRoute ∧
            hsame provenance (append ledger replay) ∧ hsame name accepted ∧
              hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier queryRoute ledgerRoute
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  have routeMatchesLedger : hsame route ledgeredRoute :=
    cont_respects_hsame queryMatchesAxiom (hsame_refl replay) axiomReplayRoute ledgerRoute
  exact
    ⟨queryMatchesAxiom, routeMatchesLedger, provenanceSame, nameAccepted,
      nameLedger⟩

theorem KernelAcceptanceAuditWitnessCarrier_source_query_route_exhaustion
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      acceptedRoute queryBoundary routePrime : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont generated candidate acceptedRoute →
        Cont acceptedRoute ledger queryBoundary →
          Cont queryBoundary replay routePrime →
            hsame accepted acceptedRoute ∧ hsame axiomQuery queryBoundary ∧
              hsame route routePrime ∧ hsame name accepted ∧ hsame name ledger := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier sourceRoute queryRoute replayRoute
  obtain ⟨generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have acceptedMatchesRoute : hsame accepted acceptedRoute :=
    cont_respects_hsame (hsame_refl generated) (hsame_refl candidate)
      generatedCandidateAccepted sourceRoute
  have queryMatchesBoundary : hsame axiomQuery queryBoundary :=
    cont_respects_hsame acceptedMatchesRoute (hsame_refl ledger)
      acceptedLedgerAxiom queryRoute
  have routeMatchesPrime : hsame route routePrime :=
    cont_respects_hsame queryMatchesBoundary (hsame_refl replay)
      axiomReplayRoute replayRoute
  exact
    ⟨acceptedMatchesRoute, queryMatchesBoundary, routeMatchesPrime, nameAccepted,
      nameLedger⟩

theorem KernelAcceptanceAuditWitnessCarrier_axiom_query_boundary
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary replayRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont axiomQuery replay replayRoute →
          SemanticNameCert
              (fun row : BHist =>
                KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger
                    axiomQuery replay transport route provenance name ∧
                  hsame row queryBoundary)
              (fun row : BHist => Cont accepted ledger row ∧ hsame row axiomQuery)
              (fun row : BHist =>
                Cont row replay replayRoute ∧ hsame replayRoute route ∧ hsame name ledger)
              hsame ∧
            hsame axiomQuery queryBoundary ∧ hsame replayRoute route := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryRoute replayRead
  have carrierWitness := carrier
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, _nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom queryRoute
  have replayMatchesRoute : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  have queryBoundaryAxiom : hsame queryBoundary axiomQuery :=
    hsame_symm queryMatchesAxiom
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery
                replay transport route provenance name ∧
              hsame row queryBoundary)
          (fun row : BHist => Cont accepted ledger row ∧ hsame row axiomQuery)
          (fun row : BHist =>
            Cont row replay replayRoute ∧ hsame replayRoute route ∧ hsame name ledger)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro queryBoundary
          (And.intro carrierWitness (hsame_refl queryBoundary))
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
          ⟨cont_result_hsame_transport queryRoute (hsame_symm source.right),
            hsame_trans source.right queryBoundaryAxiom⟩
      ledger_sound := by
        intro row source
        have rowReplayRoute : Cont row replay replayRoute := by
          cases source.right
          cases queryMatchesAxiom
          exact replayRead
        exact
          ⟨rowReplayRoute, replayMatchesRoute, nameLedger⟩
    }
  exact ⟨cert, queryMatchesAxiom, replayMatchesRoute⟩

theorem KernelAcceptanceAuditWitnessCarrier_public_obligation_surface
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary ledgeredRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont queryBoundary replay ledgeredRoute →
          SemanticNameCert (fun row : BHist => hsame row name)
              (fun row : BHist => hsame row accepted ∧ hsame row ledger)
              (fun _row : BHist =>
                Cont accepted ledger queryBoundary ∧ Cont queryBoundary replay ledgeredRoute ∧
                  hsame axiomQuery queryBoundary ∧ hsame route ledgeredRoute ∧
                    hsame name accepted ∧ hsame name ledger ∧
                      hsame provenance (append ledger replay))
              hsame ∧ hsame axiomQuery queryBoundary ∧ hsame route ledgeredRoute := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier queryRoute ledgerRoute
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
            Cont accepted ledger queryBoundary ∧ Cont queryBoundary replay ledgeredRoute ∧
              hsame axiomQuery queryBoundary ∧ hsame route ledgeredRoute ∧
                hsame name accepted ∧ hsame name ledger ∧
                  hsame provenance (append ledger replay))
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
        exact
          ⟨queryRoute, ledgerRoute, queryMatchesAxiom, routeMatchesLedger, nameAccepted,
            nameLedger, provenanceSame⟩
    }
  exact ⟨cert, queryMatchesAxiom, routeMatchesLedger⟩

theorem KernelAcceptanceAuditWitnessCarrier_acceptance_boundary
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      acceptedRoute ledgerRoute queryBoundary replayRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont generated candidate acceptedRoute →
        Cont acceptedRoute ledger ledgerRoute →
          Cont ledgerRoute replay queryBoundary →
            Cont axiomQuery replay replayRoute →
              SemanticNameCert
                  (fun row : BHist =>
                    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger
                        axiomQuery replay transport route provenance name ∧
                      hsame row acceptedRoute)
                  (fun row : BHist => Cont generated candidate row ∧ hsame row accepted)
                  (fun _row : BHist =>
                    Cont accepted ledger ledgerRoute ∧ Cont axiomQuery replay replayRoute ∧
                      hsame name ledger)
                  hsame ∧
                hsame accepted acceptedRoute ∧ hsame axiomQuery ledgerRoute ∧
                  hsame replayRoute route := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro carrier sourceRoute ledgerRead queryRead replayRead
  have carrierWitness := carrier
  obtain ⟨generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have acceptedMatchesRoute : hsame accepted acceptedRoute :=
    cont_respects_hsame (hsame_refl generated) (hsame_refl candidate)
      generatedCandidateAccepted sourceRoute
  have queryMatchesLedgerRoute : hsame axiomQuery ledgerRoute :=
    cont_respects_hsame acceptedMatchesRoute (hsame_refl ledger)
      acceptedLedgerAxiom ledgerRead
  have replayMatchesRoute : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  have acceptedLedgerRoute : Cont accepted ledger ledgerRoute := by
    cases acceptedMatchesRoute
    exact ledgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery
                replay transport route provenance name ∧
              hsame row acceptedRoute)
          (fun row : BHist => Cont generated candidate row ∧ hsame row accepted)
          (fun _row : BHist =>
            Cont accepted ledger ledgerRoute ∧ Cont axiomQuery replay replayRoute ∧
              hsame name ledger)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro acceptedRoute (And.intro carrierWitness (hsame_refl acceptedRoute))
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
          ⟨cont_result_hsame_transport sourceRoute (hsame_symm source.right),
            hsame_trans source.right (hsame_symm acceptedMatchesRoute)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨acceptedLedgerRoute, replayRead, nameLedger⟩
    }
  exact ⟨cert, acceptedMatchesRoute, queryMatchesLedgerRoute, replayMatchesRoute⟩

theorem KernelAcceptanceAuditWitnessCarrier_ledger_non_escape
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      queryBoundary replayRoute : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont axiomQuery replay replayRoute →
          hsame axiomQuery queryBoundary ∧ hsame replayRoute route ∧ hsame name accepted ∧
            hsame name ledger ∧ hsame provenance (append ledger replay) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier acceptedLedgerRead replayRead
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom acceptedLedgerRead
  have replayMatchesRoute : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  exact
    ⟨queryMatchesAxiom, replayMatchesRoute, nameAccepted, nameLedger, provenanceSame⟩

theorem KernelAcceptanceAuditWitnessCarrier_replay_query_nonescape
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      replayRoute queryBoundary terminalRead : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont accepted ledger queryBoundary →
        Cont axiomQuery replay replayRoute →
          Cont queryBoundary name terminalRead →
            hsame axiomQuery queryBoundary ∧ hsame replayRoute route ∧
              hsame name accepted ∧ hsame name ledger ∧
                Cont queryBoundary name terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier acceptedLedgerRead replayRead terminalRoute
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  have queryMatchesAxiom : hsame axiomQuery queryBoundary :=
    cont_deterministic acceptedLedgerAxiom acceptedLedgerRead
  have replayMatchesRoute : hsame replayRoute route :=
    cont_respects_hsame (hsame_refl axiomQuery) (hsame_refl replay) replayRead
      axiomReplayRoute
  exact ⟨queryMatchesAxiom, replayMatchesRoute, nameAccepted, nameLedger, terminalRoute⟩

def KernelAcceptanceAuditWitnessTerminalRow
    (accepted ledger axiomQuery replay name terminalRead : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  Cont accepted ledger axiomQuery ∧ Cont axiomQuery replay terminalRead ∧
    hsame name accepted ∧ hsame name ledger

theorem KernelAcceptanceAuditWitnessTerminalRow_boundary
    {generated candidate accepted ledger axiomQuery replay transport route provenance name
      terminalRead : BHist} :
    KernelAcceptanceAuditWitnessCarrier generated candidate accepted ledger axiomQuery replay
        transport route provenance name →
      Cont axiomQuery replay terminalRead →
        KernelAcceptanceAuditWitnessTerminalRow accepted ledger axiomQuery replay name
          terminalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier terminalRoute
  obtain ⟨_generatedCandidateAccepted, acceptedLedgerAxiom, _axiomReplayRoute,
    _transportSame, _provenanceSame, nameAccepted, nameLedger⟩ := carrier
  exact ⟨acceptedLedgerAxiom, terminalRoute, nameAccepted, nameLedger⟩

end BEDC.Derived.KernelAcceptanceAuditWitnessUp
