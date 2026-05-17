import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditExportFirewallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditExportFirewallUp : Type where
  | mk :
      (claim positive audit failure registry consistency ledger transport replay provenance
        name : BHist) →
      AuditExportFirewallUp
  deriving DecidableEq

def auditExportFirewallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditExportFirewallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditExportFirewallEncodeBHist h

def auditExportFirewallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditExportFirewallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditExportFirewallDecodeBHist tail)

private theorem auditExportFirewallDecode_encode_bhist :
    ∀ h : BHist, auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem auditExportFirewall_mk_congr
    {claim claim' positive positive' audit audit' failure failure' registry registry'
      consistency consistency' ledger ledger' transport transport' replay replay'
      provenance provenance' name name' : BHist}
    (hClaim : claim' = claim)
    (hPositive : positive' = positive)
    (hAudit : audit' = audit)
    (hFailure : failure' = failure)
    (hRegistry : registry' = registry)
    (hConsistency : consistency' = consistency)
    (hLedger : ledger' = ledger)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    AuditExportFirewallUp.mk claim' positive' audit' failure' registry' consistency'
        ledger' transport' replay' provenance' name' =
      AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
        transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hClaim
  cases hPositive
  cases hAudit
  cases hFailure
  cases hRegistry
  cases hConsistency
  cases hLedger
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def auditExportFirewallToEventFlow : AuditExportFirewallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
      transport replay provenance name =>
      [[BMark.b0],
        auditExportFirewallEncodeBHist claim,
        [BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist positive,
        [BMark.b1, BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist registry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist consistency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditExportFirewallEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditExportFirewallEncodeBHist name]

def auditExportFirewallFromEventFlow : EventFlow → Option AuditExportFirewallUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | claim :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | positive :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | audit :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | failure :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | registry :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | consistency :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | ledger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | replay :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (AuditExportFirewallUp.mk
                                                                                                  (auditExportFirewallDecodeBHist claim)
                                                                                                  (auditExportFirewallDecodeBHist positive)
                                                                                                  (auditExportFirewallDecodeBHist audit)
                                                                                                  (auditExportFirewallDecodeBHist failure)
                                                                                                  (auditExportFirewallDecodeBHist registry)
                                                                                                  (auditExportFirewallDecodeBHist consistency)
                                                                                                  (auditExportFirewallDecodeBHist ledger)
                                                                                                  (auditExportFirewallDecodeBHist transport)
                                                                                                  (auditExportFirewallDecodeBHist replay)
                                                                                                  (auditExportFirewallDecodeBHist provenance)
                                                                                                  (auditExportFirewallDecodeBHist name))
                                                                                          | _ :: _ => none

private theorem auditExportFirewall_round_trip :
    ∀ x : AuditExportFirewallUp,
      auditExportFirewallFromEventFlow (auditExportFirewallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk claim positive audit failure registry consistency ledger transport replay provenance name =>
      change
        some
          (AuditExportFirewallUp.mk
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist claim))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist positive))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist audit))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist failure))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist registry))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist consistency))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist ledger))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist transport))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist replay))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist provenance))
            (auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist name))) =
          some
            (AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger
              transport replay provenance name)
      exact
        congrArg some
          (auditExportFirewall_mk_congr
            (auditExportFirewallDecode_encode_bhist claim)
            (auditExportFirewallDecode_encode_bhist positive)
            (auditExportFirewallDecode_encode_bhist audit)
            (auditExportFirewallDecode_encode_bhist failure)
            (auditExportFirewallDecode_encode_bhist registry)
            (auditExportFirewallDecode_encode_bhist consistency)
            (auditExportFirewallDecode_encode_bhist ledger)
            (auditExportFirewallDecode_encode_bhist transport)
            (auditExportFirewallDecode_encode_bhist replay)
            (auditExportFirewallDecode_encode_bhist provenance)
            (auditExportFirewallDecode_encode_bhist name))

private theorem auditExportFirewallToEventFlow_injective
    {x y : AuditExportFirewallUp} :
    auditExportFirewallToEventFlow x = auditExportFirewallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditExportFirewallFromEventFlow (auditExportFirewallToEventFlow x) =
        auditExportFirewallFromEventFlow (auditExportFirewallToEventFlow y) :=
    congrArg auditExportFirewallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditExportFirewall_round_trip x).symm
      (Eq.trans hread (auditExportFirewall_round_trip y)))

instance auditExportFirewallBHistCarrier : BHistCarrier AuditExportFirewallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditExportFirewallToEventFlow
  fromEventFlow := auditExportFirewallFromEventFlow

instance auditExportFirewallChapterTasteGate :
    ChapterTasteGate AuditExportFirewallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditExportFirewallFromEventFlow (auditExportFirewallToEventFlow x) = some x
    exact auditExportFirewall_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditExportFirewallToEventFlow_injective heq)

def auditExportFirewallFields : AuditExportFirewallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditExportFirewallUp.mk claim positive audit failure registry consistency ledger transport
      replay provenance name =>
      [claim, positive, audit, failure, registry, consistency, ledger, transport, replay,
        provenance, name]

private theorem auditExportFirewall_field_faithful_concrete :
    ∀ x y : AuditExportFirewallUp,
      auditExportFirewallFields x = auditExportFirewallFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk claim positive audit failure registry consistency ledger transport replay provenance name =>
      cases y with
      | mk claim' positive' audit' failure' registry' consistency' ledger' transport' replay'
          provenance' name' =>
          injection hfields with hClaim tail0
          injection tail0 with hPositive tail1
          injection tail1 with hAudit tail2
          injection tail2 with hFailure tail3
          injection tail3 with hRegistry tail4
          injection tail4 with hConsistency tail5
          injection tail5 with hLedger tail6
          injection tail6 with hTransport tail7
          injection tail7 with hReplay tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hName _hNil
          cases hClaim
          cases hPositive
          cases hAudit
          cases hFailure
          cases hRegistry
          cases hConsistency
          cases hLedger
          cases hTransport
          cases hReplay
          cases hProvenance
          cases hName
          rfl

instance auditExportFirewallFieldFaithful : FieldFaithful AuditExportFirewallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditExportFirewallFields
  field_faithful := auditExportFirewall_field_faithful_concrete

private def auditExportFirewall_nontrivial_witness :
    Σ' (x : AuditExportFirewallUp) (y : AuditExportFirewallUp), x ≠ y :=
  ⟨AuditExportFirewallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    AuditExportFirewallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      -- BEDC touchpoint anchor: BHist BMark
      intro h
      cases h⟩

instance auditExportFirewallNontrivial : Nontrivial AuditExportFirewallUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair := auditExportFirewall_nontrivial_witness

theorem AuditExportFirewallTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditExportFirewallDecodeBHist (auditExportFirewallEncodeBHist h) = h) ∧
      (∀ x : AuditExportFirewallUp,
        auditExportFirewallFromEventFlow (auditExportFirewallToEventFlow x) = some x) ∧
        (∀ x y : AuditExportFirewallUp,
          auditExportFirewallToEventFlow x = auditExportFirewallToEventFlow y → x = y) ∧
          auditExportFirewallEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditExportFirewallDecode_encode_bhist
  · constructor
    · exact auditExportFirewall_round_trip
    · constructor
      · intro x y heq
        exact auditExportFirewallToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditExportFirewallUp
