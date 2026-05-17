import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditAxisSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditAxisSeparationUp : Type where
  | mk :
      (theory formal target bridge refusal exportRow transport replay provenance name : BHist) →
      AuditAxisSeparationUp
  deriving DecidableEq

def auditAxisSeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditAxisSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditAxisSeparationEncodeBHist h

def auditAxisSeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditAxisSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditAxisSeparationDecodeBHist tail)

private theorem auditAxisSeparation_decode_encode_bhist :
    ∀ h : BHist, auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditAxisSeparationFields : AuditAxisSeparationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditAxisSeparationUp.mk theory formal target bridge refusal exportRow transport replay
      provenance name =>
      [theory, formal, target, bridge, refusal, exportRow, transport, replay, provenance, name]

def auditAxisSeparationToEventFlow : AuditAxisSeparationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map auditAxisSeparationEncodeBHist (auditAxisSeparationFields x)

def auditAxisSeparationFromEventFlow : EventFlow → Option AuditAxisSeparationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | theory :: rest0 =>
      match rest0 with
      | [] => none
      | formal :: rest1 =>
          match rest1 with
          | [] => none
          | target :: rest2 =>
              match rest2 with
              | [] => none
              | bridge :: rest3 =>
                  match rest3 with
                  | [] => none
                  | refusal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | exportRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (AuditAxisSeparationUp.mk
                                                  (auditAxisSeparationDecodeBHist theory)
                                                  (auditAxisSeparationDecodeBHist formal)
                                                  (auditAxisSeparationDecodeBHist target)
                                                  (auditAxisSeparationDecodeBHist bridge)
                                                  (auditAxisSeparationDecodeBHist refusal)
                                                  (auditAxisSeparationDecodeBHist exportRow)
                                                  (auditAxisSeparationDecodeBHist transport)
                                                  (auditAxisSeparationDecodeBHist replay)
                                                  (auditAxisSeparationDecodeBHist provenance)
                                                  (auditAxisSeparationDecodeBHist name))
                                          | _ :: _ => none

private theorem auditAxisSeparation_round_trip :
    ∀ x : AuditAxisSeparationUp,
      auditAxisSeparationFromEventFlow (auditAxisSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk theory formal target bridge refusal exportRow transport replay provenance name =>
      change
        some
          (AuditAxisSeparationUp.mk
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist theory))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist formal))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist target))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist bridge))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist refusal))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist exportRow))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist transport))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist replay))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist provenance))
            (auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist name))) =
          some
            (AuditAxisSeparationUp.mk theory formal target bridge refusal exportRow transport
              replay provenance name)
      rw [auditAxisSeparation_decode_encode_bhist theory,
        auditAxisSeparation_decode_encode_bhist formal,
        auditAxisSeparation_decode_encode_bhist target,
        auditAxisSeparation_decode_encode_bhist bridge,
        auditAxisSeparation_decode_encode_bhist refusal,
        auditAxisSeparation_decode_encode_bhist exportRow,
        auditAxisSeparation_decode_encode_bhist transport,
        auditAxisSeparation_decode_encode_bhist replay,
        auditAxisSeparation_decode_encode_bhist provenance,
        auditAxisSeparation_decode_encode_bhist name]

private theorem auditAxisSeparationToEventFlow_injective {x y : AuditAxisSeparationUp} :
    auditAxisSeparationToEventFlow x = auditAxisSeparationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditAxisSeparationFromEventFlow (auditAxisSeparationToEventFlow x) =
        auditAxisSeparationFromEventFlow (auditAxisSeparationToEventFlow y) :=
    congrArg auditAxisSeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditAxisSeparation_round_trip x).symm
      (Eq.trans hread (auditAxisSeparation_round_trip y)))

private theorem auditAxisSeparation_field_faithful :
    ∀ x y : AuditAxisSeparationUp, auditAxisSeparationFields x = auditAxisSeparationFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk theory₁ formal₁ target₁ bridge₁ refusal₁ exportRow₁ transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk theory₂ formal₂ target₂ bridge₂ refusal₂ exportRow₂ transport₂ replay₂ provenance₂ name₂ =>
          cases h
          rfl

instance auditAxisSeparationBHistCarrier : BHistCarrier AuditAxisSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditAxisSeparationToEventFlow
  fromEventFlow := auditAxisSeparationFromEventFlow

instance auditAxisSeparationChapterTasteGate : ChapterTasteGate AuditAxisSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditAxisSeparationFromEventFlow (auditAxisSeparationToEventFlow x) = some x
    exact auditAxisSeparation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditAxisSeparationToEventFlow_injective heq)

instance auditAxisSeparationFieldFaithful : FieldFaithful AuditAxisSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditAxisSeparationFields
  field_faithful := auditAxisSeparation_field_faithful

instance auditAxisSeparationNontrivial : Nontrivial AuditAxisSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditAxisSeparationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditAxisSeparationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditAxisSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditAxisSeparationChapterTasteGate

theorem AuditAxisSeparationTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditAxisSeparationDecodeBHist (auditAxisSeparationEncodeBHist h) = h) ∧
      (∀ x : AuditAxisSeparationUp,
        auditAxisSeparationFromEventFlow (auditAxisSeparationToEventFlow x) = some x) ∧
        (∀ x y : AuditAxisSeparationUp,
          auditAxisSeparationFields x = auditAxisSeparationFields y → x = y) ∧
          (∃ x y : AuditAxisSeparationUp, x ≠ y) ∧
            auditAxisSeparationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditAxisSeparation_decode_encode_bhist
  · constructor
    · exact auditAxisSeparation_round_trip
    · constructor
      · exact auditAxisSeparation_field_faithful
      · constructor
        · exact ⟨Nontrivial.witness_pair.1, Nontrivial.witness_pair.2.1,
            Nontrivial.witness_pair.2.2⟩
        · rfl

end BEDC.Derived.AuditAxisSeparationUp
