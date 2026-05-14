import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditGateFailureWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditGateFailureWitnessUp : Type where
  | mk : (gate failed refusal diagnostic transport route provenance name : BHist) →
      AuditGateFailureWitnessUp
  deriving DecidableEq

def auditGateFailureWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditGateFailureWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditGateFailureWitnessEncodeBHist h

def auditGateFailureWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditGateFailureWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditGateFailureWitnessDecodeBHist tail)

private theorem auditGateFailureWitness_decode_encode_bhist :
    ∀ h : BHist,
      auditGateFailureWitnessDecodeBHist
        (auditGateFailureWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditGateFailureWitnessToEventFlow : AuditGateFailureWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditGateFailureWitnessUp.mk gate failed refusal diagnostic transport route provenance name =>
      [[BMark.b0],
        auditGateFailureWitnessEncodeBHist gate,
        [BMark.b1, BMark.b0],
        auditGateFailureWitnessEncodeBHist failed,
        [BMark.b1, BMark.b1, BMark.b0],
        auditGateFailureWitnessEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateFailureWitnessEncodeBHist diagnostic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateFailureWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateFailureWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateFailureWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditGateFailureWitnessEncodeBHist name]

def auditGateFailureWitnessFromEventFlow :
    EventFlow → Option AuditGateFailureWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gate :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | failed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | diagnostic :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (AuditGateFailureWitnessUp.mk
                                                                          (auditGateFailureWitnessDecodeBHist gate)
                                                                          (auditGateFailureWitnessDecodeBHist failed)
                                                                          (auditGateFailureWitnessDecodeBHist refusal)
                                                                          (auditGateFailureWitnessDecodeBHist diagnostic)
                                                                          (auditGateFailureWitnessDecodeBHist transport)
                                                                          (auditGateFailureWitnessDecodeBHist route)
                                                                          (auditGateFailureWitnessDecodeBHist provenance)
                                                                          (auditGateFailureWitnessDecodeBHist name))
                                                                  | _ :: _ => none

private theorem auditGateFailureWitness_round_trip :
    ∀ x : AuditGateFailureWitnessUp,
      auditGateFailureWitnessFromEventFlow
        (auditGateFailureWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gate failed refusal diagnostic transport route provenance name =>
      change
        some
          (AuditGateFailureWitnessUp.mk
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist gate))
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist failed))
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist refusal))
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist diagnostic))
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist transport))
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist route))
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist provenance))
            (auditGateFailureWitnessDecodeBHist
              (auditGateFailureWitnessEncodeBHist name))) =
          some
            (AuditGateFailureWitnessUp.mk gate failed refusal diagnostic transport
              route provenance name)
      rw [auditGateFailureWitness_decode_encode_bhist gate,
        auditGateFailureWitness_decode_encode_bhist failed,
        auditGateFailureWitness_decode_encode_bhist refusal,
        auditGateFailureWitness_decode_encode_bhist diagnostic,
        auditGateFailureWitness_decode_encode_bhist transport,
        auditGateFailureWitness_decode_encode_bhist route,
        auditGateFailureWitness_decode_encode_bhist provenance,
        auditGateFailureWitness_decode_encode_bhist name]

private theorem auditGateFailureWitnessToEventFlow_injective
    {x y : AuditGateFailureWitnessUp} :
    auditGateFailureWitnessToEventFlow x =
      auditGateFailureWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditGateFailureWitnessFromEventFlow
          (auditGateFailureWitnessToEventFlow x) =
        auditGateFailureWitnessFromEventFlow
          (auditGateFailureWitnessToEventFlow y) :=
    congrArg auditGateFailureWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditGateFailureWitness_round_trip x).symm
      (Eq.trans hread (auditGateFailureWitness_round_trip y)))

def auditGateFailureWitnessFields : AuditGateFailureWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditGateFailureWitnessUp.mk gate failed refusal diagnostic transport route provenance name =>
      [gate, failed, refusal, diagnostic, transport, route, provenance, name]

private theorem AuditGateFailureWitnessTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : AuditGateFailureWitnessUp,
      auditGateFailureWitnessFields x = auditGateFailureWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk gate failed refusal diagnostic transport route provenance name =>
      cases y with
      | mk gate' failed' refusal' diagnostic' transport' route' provenance' name' =>
          cases hfields
          rfl

instance auditGateFailureWitnessBHistCarrier :
    BHistCarrier AuditGateFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditGateFailureWitnessToEventFlow
  fromEventFlow := auditGateFailureWitnessFromEventFlow

instance auditGateFailureWitnessChapterTasteGate :
    ChapterTasteGate AuditGateFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      auditGateFailureWitnessFromEventFlow
        (auditGateFailureWitnessToEventFlow x) = some x
    exact auditGateFailureWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditGateFailureWitnessToEventFlow_injective heq)

instance auditGateFailureWitnessFieldFaithful :
    FieldFaithful AuditGateFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditGateFailureWitnessFields
  field_faithful := AuditGateFailureWitnessTasteGate_single_carrier_alignment_field_faithful

theorem AuditGateFailureWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditGateFailureWitnessDecodeBHist
      (auditGateFailureWitnessEncodeBHist h) = h) ∧
      (∀ x : AuditGateFailureWitnessUp,
        auditGateFailureWitnessFromEventFlow
          (auditGateFailureWitnessToEventFlow x) = some x) ∧
      (∀ x y : AuditGateFailureWitnessUp,
        auditGateFailureWitnessToEventFlow x =
          auditGateFailureWitnessToEventFlow y → x = y) ∧
      auditGateFailureWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact auditGateFailureWitness_decode_encode_bhist
  · constructor
    · exact auditGateFailureWitness_round_trip
    · constructor
      · intro x y heq
        exact auditGateFailureWitnessToEventFlow_injective heq
      · rfl

theorem AuditGateFailureWitnessUp_obligation_surface :
    Nonempty (BHistCarrier AuditGateFailureWitnessUp) ∧
      Nonempty (ChapterTasteGate AuditGateFailureWitnessUp) ∧
      ∃ x : AuditGateFailureWitnessUp,
        x =
            AuditGateFailureWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  let x : AuditGateFailureWitnessUp :=
    AuditGateFailureWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty
  constructor
  · exact ⟨auditGateFailureWitnessBHistCarrier⟩
  · constructor
    · exact ⟨auditGateFailureWitnessChapterTasteGate⟩
    · exact ⟨x, rfl, ChapterTasteGate.round_trip x⟩

end BEDC.Derived.AuditGateFailureWitnessUp
