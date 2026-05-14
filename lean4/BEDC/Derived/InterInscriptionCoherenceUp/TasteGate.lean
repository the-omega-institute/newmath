import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InterInscriptionCoherenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InterInscriptionCoherenceUp : Type where
  | mk :
      (leftInscription rightInscription localityLedger transportRow routeRow provenance
        nameRow : BHist) →
      InterInscriptionCoherenceUp
  deriving DecidableEq

private def interInscriptionCoherenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: interInscriptionCoherenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: interInscriptionCoherenceEncodeBHist h

private def interInscriptionCoherenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (interInscriptionCoherenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (interInscriptionCoherenceDecodeBHist tail)

private theorem interInscriptionCoherenceDecode_encode_bhist :
    ∀ h : BHist,
      interInscriptionCoherenceDecodeBHist
        (interInscriptionCoherenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def interInscriptionCoherenceToEventFlow :
    InterInscriptionCoherenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InterInscriptionCoherenceUp.mk leftInscription rightInscription localityLedger
      transportRow routeRow provenance nameRow =>
      [[BMark.b0],
        interInscriptionCoherenceEncodeBHist leftInscription,
        [BMark.b1, BMark.b0],
        interInscriptionCoherenceEncodeBHist rightInscription,
        [BMark.b1, BMark.b1, BMark.b0],
        interInscriptionCoherenceEncodeBHist localityLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interInscriptionCoherenceEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interInscriptionCoherenceEncodeBHist routeRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interInscriptionCoherenceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interInscriptionCoherenceEncodeBHist nameRow]

private def interInscriptionCoherenceFromEventFlow :
    EventFlow → Option InterInscriptionCoherenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | leftInscription :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rightInscription :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | localityLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transportRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | routeRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nameRow :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (InterInscriptionCoherenceUp.mk
                                                                  (interInscriptionCoherenceDecodeBHist
                                                                    leftInscription)
                                                                  (interInscriptionCoherenceDecodeBHist
                                                                    rightInscription)
                                                                  (interInscriptionCoherenceDecodeBHist
                                                                    localityLedger)
                                                                  (interInscriptionCoherenceDecodeBHist
                                                                    transportRow)
                                                                  (interInscriptionCoherenceDecodeBHist
                                                                    routeRow)
                                                                  (interInscriptionCoherenceDecodeBHist
                                                                    provenance)
                                                                  (interInscriptionCoherenceDecodeBHist
                                                                    nameRow))
                                                          | _ :: _ => none

private theorem interInscriptionCoherence_round_trip :
    ∀ x : InterInscriptionCoherenceUp,
      interInscriptionCoherenceFromEventFlow
        (interInscriptionCoherenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftInscription rightInscription localityLedger transportRow routeRow provenance
      nameRow =>
      change
        some
          (InterInscriptionCoherenceUp.mk
            (interInscriptionCoherenceDecodeBHist
              (interInscriptionCoherenceEncodeBHist leftInscription))
            (interInscriptionCoherenceDecodeBHist
              (interInscriptionCoherenceEncodeBHist rightInscription))
            (interInscriptionCoherenceDecodeBHist
              (interInscriptionCoherenceEncodeBHist localityLedger))
            (interInscriptionCoherenceDecodeBHist
              (interInscriptionCoherenceEncodeBHist transportRow))
            (interInscriptionCoherenceDecodeBHist
              (interInscriptionCoherenceEncodeBHist routeRow))
            (interInscriptionCoherenceDecodeBHist
              (interInscriptionCoherenceEncodeBHist provenance))
            (interInscriptionCoherenceDecodeBHist
              (interInscriptionCoherenceEncodeBHist nameRow))) =
          some
            (InterInscriptionCoherenceUp.mk leftInscription rightInscription localityLedger
              transportRow routeRow provenance nameRow)
      rw [interInscriptionCoherenceDecode_encode_bhist leftInscription,
        interInscriptionCoherenceDecode_encode_bhist rightInscription,
        interInscriptionCoherenceDecode_encode_bhist localityLedger,
        interInscriptionCoherenceDecode_encode_bhist transportRow,
        interInscriptionCoherenceDecode_encode_bhist routeRow,
        interInscriptionCoherenceDecode_encode_bhist provenance,
        interInscriptionCoherenceDecode_encode_bhist nameRow]

private theorem interInscriptionCoherenceToEventFlow_injective
    {x y : InterInscriptionCoherenceUp} :
    interInscriptionCoherenceToEventFlow x =
      interInscriptionCoherenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      interInscriptionCoherenceFromEventFlow
          (interInscriptionCoherenceToEventFlow x) =
        interInscriptionCoherenceFromEventFlow
          (interInscriptionCoherenceToEventFlow y) :=
    congrArg interInscriptionCoherenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (interInscriptionCoherence_round_trip x).symm
      (Eq.trans hread (interInscriptionCoherence_round_trip y)))

private def interInscriptionCoherenceFields :
    InterInscriptionCoherenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InterInscriptionCoherenceUp.mk leftInscription rightInscription localityLedger
      transportRow routeRow provenance nameRow =>
      [leftInscription, rightInscription, localityLedger, transportRow, routeRow, provenance,
        nameRow]

private theorem interInscriptionCoherenceFields_faithful :
    ∀ x y : InterInscriptionCoherenceUp,
      interInscriptionCoherenceFields x = interInscriptionCoherenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk left₁ right₁ locality₁ transport₁ route₁ provenance₁ name₁ =>
      cases y with
      | mk left₂ right₂ locality₂ transport₂ route₂ provenance₂ name₂ =>
          change
            [left₁, right₁, locality₁, transport₁, route₁, provenance₁, name₁] =
              [left₂, right₂, locality₂, transport₂, route₂, provenance₂, name₂] at h
          cases h
          rfl

instance interInscriptionCoherenceBHistCarrier :
    BHistCarrier InterInscriptionCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := interInscriptionCoherenceToEventFlow
  fromEventFlow := interInscriptionCoherenceFromEventFlow

instance interInscriptionCoherenceChapterTasteGate :
    ChapterTasteGate InterInscriptionCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      interInscriptionCoherenceFromEventFlow
        (interInscriptionCoherenceToEventFlow x) = some x
    exact interInscriptionCoherence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (interInscriptionCoherenceToEventFlow_injective heq)

instance interInscriptionCoherenceFieldFaithful :
    FieldFaithful InterInscriptionCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := interInscriptionCoherenceFields
  field_faithful := interInscriptionCoherenceFields_faithful

instance interInscriptionCoherenceNontrivial :
    Nontrivial InterInscriptionCoherenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InterInscriptionCoherenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      InterInscriptionCoherenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InterInscriptionCoherenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  interInscriptionCoherenceChapterTasteGate

theorem InterInscriptionCoherenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      interInscriptionCoherenceDecodeBHist
        (interInscriptionCoherenceEncodeBHist h) = h) ∧
      (∀ x : InterInscriptionCoherenceUp,
        interInscriptionCoherenceFromEventFlow
          (interInscriptionCoherenceToEventFlow x) = some x) ∧
        (∀ x y : InterInscriptionCoherenceUp,
          interInscriptionCoherenceToEventFlow x =
            interInscriptionCoherenceToEventFlow y → x = y) ∧
          interInscriptionCoherenceEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : InterInscriptionCoherenceUp,
              interInscriptionCoherenceFields x =
                interInscriptionCoherenceFields y → x = y) ∧
              (∃ x y : InterInscriptionCoherenceUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact interInscriptionCoherenceDecode_encode_bhist
  · constructor
    · exact interInscriptionCoherence_round_trip
    · constructor
      · intro x y heq
        exact interInscriptionCoherenceToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact interInscriptionCoherenceFields_faithful
          · exact
              ⟨InterInscriptionCoherenceUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                InterInscriptionCoherenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.InterInscriptionCoherenceUp
