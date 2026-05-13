import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapMethodologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapMethodologyUp : Type where
  | mk :
      (template admittedFamily classifier obligation frontier boundary handoff transport route
        provenance name : BHist) →
      AuditMapMethodologyUp
  deriving DecidableEq

def auditMapMethodologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapMethodologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapMethodologyEncodeBHist h

def auditMapMethodologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapMethodologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapMethodologyDecodeBHist tail)

private theorem auditMapMethodology_decode_encode_bhist :
    ∀ h : BHist,
      auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditMapMethodologyFields : AuditMapMethodologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapMethodologyUp.mk template admittedFamily classifier obligation frontier boundary
      handoff transport route provenance name =>
      [template, admittedFamily, classifier, obligation, frontier, boundary, handoff,
        transport, route, provenance, name]

def auditMapMethodologyToEventFlow : AuditMapMethodologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapMethodologyUp.mk template admittedFamily classifier obligation frontier boundary
      handoff transport route provenance name =>
      [[BMark.b0],
        auditMapMethodologyEncodeBHist template,
        [BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist admittedFamily,
        [BMark.b1, BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist obligation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditMapMethodologyEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditMapMethodologyEncodeBHist name]

def auditMapMethodologyFromEventFlow : EventFlow → Option AuditMapMethodologyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | template :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | admittedFamily :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | obligation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | frontier :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | boundary :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | handoff :: rest13 =>
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
                                                                      | route :: rest17 =>
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
                                                                                                (AuditMapMethodologyUp.mk
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    template)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    admittedFamily)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    classifier)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    obligation)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    frontier)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    boundary)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    handoff)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    transport)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    route)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    provenance)
                                                                                                  (auditMapMethodologyDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ => none

private theorem auditMapMethodology_round_trip :
    ∀ x : AuditMapMethodologyUp,
      auditMapMethodologyFromEventFlow (auditMapMethodologyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk template admittedFamily classifier obligation frontier boundary handoff transport
      route provenance name =>
      change
        some
          (AuditMapMethodologyUp.mk
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist template))
            (auditMapMethodologyDecodeBHist
              (auditMapMethodologyEncodeBHist admittedFamily))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist classifier))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist obligation))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist frontier))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist boundary))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist handoff))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist transport))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist route))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist provenance))
            (auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist name))) =
          some
            (AuditMapMethodologyUp.mk template admittedFamily classifier obligation frontier
              boundary handoff transport route provenance name)
      rw [auditMapMethodology_decode_encode_bhist template,
        auditMapMethodology_decode_encode_bhist admittedFamily,
        auditMapMethodology_decode_encode_bhist classifier,
        auditMapMethodology_decode_encode_bhist obligation,
        auditMapMethodology_decode_encode_bhist frontier,
        auditMapMethodology_decode_encode_bhist boundary,
        auditMapMethodology_decode_encode_bhist handoff,
        auditMapMethodology_decode_encode_bhist transport,
        auditMapMethodology_decode_encode_bhist route,
        auditMapMethodology_decode_encode_bhist provenance,
        auditMapMethodology_decode_encode_bhist name]

private theorem auditMapMethodologyToEventFlow_injective
    {x y : AuditMapMethodologyUp} :
    auditMapMethodologyToEventFlow x = auditMapMethodologyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditMapMethodologyFromEventFlow (auditMapMethodologyToEventFlow x) =
        auditMapMethodologyFromEventFlow (auditMapMethodologyToEventFlow y) :=
    congrArg auditMapMethodologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditMapMethodology_round_trip x).symm
      (Eq.trans hread (auditMapMethodology_round_trip y)))

private theorem AuditMapMethodologyTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : AuditMapMethodologyUp,
      auditMapMethodologyFields x = auditMapMethodologyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk template admittedFamily classifier obligation frontier boundary handoff transport
      route provenance name =>
      cases y with
      | mk template' admittedFamily' classifier' obligation' frontier' boundary' handoff'
          transport' route' provenance' name' =>
          cases hfields
          rfl

instance auditMapMethodologyBHistCarrier : BHistCarrier AuditMapMethodologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapMethodologyToEventFlow
  fromEventFlow := auditMapMethodologyFromEventFlow

instance auditMapMethodologyChapterTasteGate :
    ChapterTasteGate AuditMapMethodologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditMapMethodologyFromEventFlow (auditMapMethodologyToEventFlow x) = some x
    exact auditMapMethodology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapMethodologyToEventFlow_injective heq)

instance auditMapMethodologyFieldFaithful :
    FieldFaithful AuditMapMethodologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditMapMethodologyFields
  field_faithful := AuditMapMethodologyTasteGate_single_carrier_alignment_field_faithful

instance auditMapMethodologyNontrivial : Nontrivial AuditMapMethodologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditMapMethodologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AuditMapMethodologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditMapMethodologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapMethodologyChapterTasteGate

theorem AuditMapMethodologyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapMethodologyDecodeBHist (auditMapMethodologyEncodeBHist h) = h) ∧
      (∀ x : AuditMapMethodologyUp,
        auditMapMethodologyFromEventFlow (auditMapMethodologyToEventFlow x) = some x) ∧
        (∀ x y : AuditMapMethodologyUp,
          auditMapMethodologyToEventFlow x = auditMapMethodologyToEventFlow y →
            x = y) ∧
          auditMapMethodologyEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : AuditMapMethodologyUp,
              auditMapMethodologyFields x = auditMapMethodologyFields y → x = y) ∧
              (∃ x y : AuditMapMethodologyUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditMapMethodology_decode_encode_bhist
  · constructor
    · exact auditMapMethodology_round_trip
    · constructor
      · intro x y heq
        exact auditMapMethodologyToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact AuditMapMethodologyTasteGate_single_carrier_alignment_field_faithful
          · exact
              ⟨AuditMapMethodologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                AuditMapMethodologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.AuditMapMethodologyUp
