import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectFreeObservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectFreeObservationUp : Type where
  | mk : (O H K D L C P N : BHist) → SubjectFreeObservationUp
  deriving DecidableEq

def subjectFreeObservationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectFreeObservationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectFreeObservationEncodeBHist h

def subjectFreeObservationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectFreeObservationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectFreeObservationDecodeBHist tail)

private theorem subjectFreeObservation_decode_encode_bhist :
    ∀ h : BHist, subjectFreeObservationDecodeBHist
      (subjectFreeObservationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subjectFreeObservationFields : SubjectFreeObservationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectFreeObservationUp.mk O H K D L C P N => [O, H, K, D, L, C, P, N]

def subjectFreeObservationToEventFlow : SubjectFreeObservationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map subjectFreeObservationEncodeBHist (subjectFreeObservationFields x)

def subjectFreeObservationFromEventFlow : EventFlow → Option SubjectFreeObservationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | O :: rest0 =>
      match rest0 with
      | [] => none
      | H :: rest1 =>
          match rest1 with
          | [] => none
          | K :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | C :: rest5 =>
                          match rest5 with
                          | [] => none
                          | P :: rest6 =>
                              match rest6 with
                              | [] => none
                              | N :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (SubjectFreeObservationUp.mk
                                          (subjectFreeObservationDecodeBHist O)
                                          (subjectFreeObservationDecodeBHist H)
                                          (subjectFreeObservationDecodeBHist K)
                                          (subjectFreeObservationDecodeBHist D)
                                          (subjectFreeObservationDecodeBHist L)
                                          (subjectFreeObservationDecodeBHist C)
                                          (subjectFreeObservationDecodeBHist P)
                                          (subjectFreeObservationDecodeBHist N))
                                  | _ :: _ => none

private theorem subjectFreeObservation_round_trip :
    ∀ x : SubjectFreeObservationUp,
      subjectFreeObservationFromEventFlow (subjectFreeObservationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O H K D L C P N =>
      change
        some
          (SubjectFreeObservationUp.mk
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist O))
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist H))
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist K))
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist D))
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist L))
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist C))
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist P))
            (subjectFreeObservationDecodeBHist (subjectFreeObservationEncodeBHist N))) =
          some (SubjectFreeObservationUp.mk O H K D L C P N)
      rw [subjectFreeObservation_decode_encode_bhist O,
        subjectFreeObservation_decode_encode_bhist H,
        subjectFreeObservation_decode_encode_bhist K,
        subjectFreeObservation_decode_encode_bhist D,
        subjectFreeObservation_decode_encode_bhist L,
        subjectFreeObservation_decode_encode_bhist C,
        subjectFreeObservation_decode_encode_bhist P,
        subjectFreeObservation_decode_encode_bhist N]

private theorem subjectFreeObservationToEventFlow_injective
    {x y : SubjectFreeObservationUp} :
    subjectFreeObservationToEventFlow x = subjectFreeObservationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectFreeObservationFromEventFlow (subjectFreeObservationToEventFlow x) =
        subjectFreeObservationFromEventFlow (subjectFreeObservationToEventFlow y) :=
    congrArg subjectFreeObservationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectFreeObservation_round_trip x).symm
      (Eq.trans hread (subjectFreeObservation_round_trip y)))

private theorem subjectFreeObservation_field_faithful :
    ∀ x y : SubjectFreeObservationUp, subjectFreeObservationFields x =
      subjectFreeObservationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ H₁ K₁ D₁ L₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ H₂ K₂ D₂ L₂ C₂ P₂ N₂ =>
          injection hfields with hO tail0
          injection tail0 with hH tail1
          injection tail1 with hK tail2
          injection tail2 with hD tail3
          injection tail3 with hL tail4
          injection tail4 with hC tail5
          injection tail5 with hP tail6
          injection tail6 with hN _
          subst hO
          subst hH
          subst hK
          subst hD
          subst hL
          subst hC
          subst hP
          subst hN
          rfl

instance subjectFreeObservationBHistCarrier : BHistCarrier SubjectFreeObservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectFreeObservationToEventFlow
  fromEventFlow := subjectFreeObservationFromEventFlow

instance subjectFreeObservationChapterTasteGate :
    ChapterTasteGate SubjectFreeObservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subjectFreeObservationFromEventFlow (subjectFreeObservationToEventFlow x) = some x
    exact subjectFreeObservation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectFreeObservationToEventFlow_injective heq)

instance subjectFreeObservationFieldFaithful :
    FieldFaithful SubjectFreeObservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := subjectFreeObservationFields
  field_faithful := subjectFreeObservation_field_faithful

instance subjectFreeObservationNontrivial : Nontrivial SubjectFreeObservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubjectFreeObservationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubjectFreeObservationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SubjectFreeObservationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subjectFreeObservationChapterTasteGate

def taste_gate_witness : ChapterTasteGate SubjectFreeObservationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subjectFreeObservationChapterTasteGate

theorem SubjectFreeObservationTasteGate_single_carrier_alignment :
    (∀ h : BHist, subjectFreeObservationDecodeBHist
      (subjectFreeObservationEncodeBHist h) = h) ∧
      (∀ x : SubjectFreeObservationUp,
        subjectFreeObservationFromEventFlow (subjectFreeObservationToEventFlow x) = some x) ∧
        (∀ x y : SubjectFreeObservationUp,
          subjectFreeObservationToEventFlow x = subjectFreeObservationToEventFlow y → x = y) ∧
          subjectFreeObservationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact subjectFreeObservation_decode_encode_bhist
  · constructor
    · exact subjectFreeObservation_round_trip
    · constructor
      · intro x y heq
        exact subjectFreeObservationToEventFlow_injective heq
      · rfl

end BEDC.Derived.SubjectFreeObservationUp
