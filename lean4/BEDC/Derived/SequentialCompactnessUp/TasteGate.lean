import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCompactnessUp : Type where
  | mk : (K S B R H C P N : BHist) → SequentialCompactnessUp
  deriving DecidableEq

def sequentialCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCompactnessEncodeBHist h

def sequentialCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCompactnessDecodeBHist tail)

private theorem sequentialCompactnessDecode_encode_bhist :
    ∀ h : BHist,
      sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sequentialCompactnessToEventFlow : SequentialCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCompactnessUp.mk K S B R H C P N =>
      [sequentialCompactnessEncodeBHist K,
        sequentialCompactnessEncodeBHist S,
        sequentialCompactnessEncodeBHist B,
        sequentialCompactnessEncodeBHist R,
        sequentialCompactnessEncodeBHist H,
        sequentialCompactnessEncodeBHist C,
        sequentialCompactnessEncodeBHist P,
        sequentialCompactnessEncodeBHist N]

def sequentialCompactnessFromEventFlow : EventFlow → Option SequentialCompactnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | K :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | H :: rest4 =>
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
                                        (SequentialCompactnessUp.mk
                                          (sequentialCompactnessDecodeBHist K)
                                          (sequentialCompactnessDecodeBHist S)
                                          (sequentialCompactnessDecodeBHist B)
                                          (sequentialCompactnessDecodeBHist R)
                                          (sequentialCompactnessDecodeBHist H)
                                          (sequentialCompactnessDecodeBHist C)
                                          (sequentialCompactnessDecodeBHist P)
                                          (sequentialCompactnessDecodeBHist N))
                                  | _ :: _ => none

def sequentialCompactnessFields : SequentialCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCompactnessUp.mk K S B R H C P N => [K, S, B, R, H, C, P, N]

private theorem sequentialCompactness_round_trip :
    ∀ x : SequentialCompactnessUp,
      sequentialCompactnessFromEventFlow (sequentialCompactnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K S B R H C P N =>
      change
        some
          (SequentialCompactnessUp.mk
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist K))
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist S))
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist B))
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist R))
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist H))
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist C))
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist P))
            (sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist N))) =
          some (SequentialCompactnessUp.mk K S B R H C P N)
      rw [sequentialCompactnessDecode_encode_bhist K,
        sequentialCompactnessDecode_encode_bhist S,
        sequentialCompactnessDecode_encode_bhist B,
        sequentialCompactnessDecode_encode_bhist R,
        sequentialCompactnessDecode_encode_bhist H,
        sequentialCompactnessDecode_encode_bhist C,
        sequentialCompactnessDecode_encode_bhist P,
        sequentialCompactnessDecode_encode_bhist N]

private theorem sequentialCompactnessToEventFlow_injective
    {x y : SequentialCompactnessUp} :
    sequentialCompactnessToEventFlow x = sequentialCompactnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCompactnessFromEventFlow (sequentialCompactnessToEventFlow x) =
        sequentialCompactnessFromEventFlow (sequentialCompactnessToEventFlow y) :=
    congrArg sequentialCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentialCompactness_round_trip x).symm
      (Eq.trans hread (sequentialCompactness_round_trip y)))

instance sequentialCompactnessBHistCarrier :
    BHistCarrier SequentialCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCompactnessToEventFlow
  fromEventFlow := sequentialCompactnessFromEventFlow

instance sequentialCompactnessChapterTasteGate :
    ChapterTasteGate SequentialCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sequentialCompactnessFromEventFlow (sequentialCompactnessToEventFlow x) = some x
    exact sequentialCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sequentialCompactnessToEventFlow_injective heq)

instance sequentialCompactnessFieldFaithful :
    FieldFaithful SequentialCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sequentialCompactnessFields
  field_faithful := by
    intro x y h
    cases x with
    | mk K₁ S₁ B₁ R₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk K₂ S₂ B₂ R₂ H₂ C₂ P₂ N₂ =>
            cases h
            rfl

instance sequentialCompactnessNontrivial :
    Nontrivial SequentialCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SequentialCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SequentialCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SequentialCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sequentialCompactnessChapterTasteGate

theorem SequentialCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      sequentialCompactnessDecodeBHist (sequentialCompactnessEncodeBHist h) = h) ∧
      (∀ x : SequentialCompactnessUp,
        sequentialCompactnessFromEventFlow (sequentialCompactnessToEventFlow x) = some x) ∧
        (∀ x y : SequentialCompactnessUp,
          sequentialCompactnessToEventFlow x = sequentialCompactnessToEventFlow y → x = y) ∧
          sequentialCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact sequentialCompactnessDecode_encode_bhist
  · constructor
    · exact sequentialCompactness_round_trip
    · constructor
      · intro x y heq
        exact sequentialCompactnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.SequentialCompactnessUp
