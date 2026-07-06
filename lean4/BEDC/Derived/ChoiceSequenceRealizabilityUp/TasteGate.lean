import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoiceSequenceRealizabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoiceSequenceRealizabilityUp : Type where
  | mk : (S R F D H T P N : BHist) → ChoiceSequenceRealizabilityUp
  deriving DecidableEq

def choiceSequenceRealizabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: choiceSequenceRealizabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: choiceSequenceRealizabilityEncodeBHist h

def choiceSequenceRealizabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (choiceSequenceRealizabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (choiceSequenceRealizabilityDecodeBHist tail)

private theorem choiceSequenceRealizabilityDecode_encode_bhist :
    ∀ h : BHist,
      choiceSequenceRealizabilityDecodeBHist
        (choiceSequenceRealizabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def choiceSequenceRealizabilityToEventFlow : ChoiceSequenceRealizabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChoiceSequenceRealizabilityUp.mk S R F D H T P N =>
      [[BMark.b0],
        choiceSequenceRealizabilityEncodeBHist S,
        [BMark.b1, BMark.b0],
        choiceSequenceRealizabilityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        choiceSequenceRealizabilityEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceSequenceRealizabilityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceSequenceRealizabilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceSequenceRealizabilityEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        choiceSequenceRealizabilityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        choiceSequenceRealizabilityEncodeBHist N]

def choiceSequenceRealizabilityFromEventFlow :
    EventFlow → Option ChoiceSequenceRealizabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | F :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | T :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ChoiceSequenceRealizabilityUp.mk
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            S)
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            R)
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            F)
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            D)
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            H)
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            T)
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            P)
                                                                          (choiceSequenceRealizabilityDecodeBHist
                                                                            N))
                                                                  | _ :: _ => none

private theorem choiceSequenceRealizability_round_trip :
    ∀ x : ChoiceSequenceRealizabilityUp,
      choiceSequenceRealizabilityFromEventFlow
        (choiceSequenceRealizabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R F D H T P N =>
      change
        some
          (ChoiceSequenceRealizabilityUp.mk
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist S))
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist R))
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist F))
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist D))
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist H))
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist T))
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist P))
            (choiceSequenceRealizabilityDecodeBHist
              (choiceSequenceRealizabilityEncodeBHist N))) =
          some (ChoiceSequenceRealizabilityUp.mk S R F D H T P N)
      rw [choiceSequenceRealizabilityDecode_encode_bhist S,
        choiceSequenceRealizabilityDecode_encode_bhist R,
        choiceSequenceRealizabilityDecode_encode_bhist F,
        choiceSequenceRealizabilityDecode_encode_bhist D,
        choiceSequenceRealizabilityDecode_encode_bhist H,
        choiceSequenceRealizabilityDecode_encode_bhist T,
        choiceSequenceRealizabilityDecode_encode_bhist P,
        choiceSequenceRealizabilityDecode_encode_bhist N]

private theorem choiceSequenceRealizabilityToEventFlow_injective
    {x y : ChoiceSequenceRealizabilityUp} :
    choiceSequenceRealizabilityToEventFlow x = choiceSequenceRealizabilityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      choiceSequenceRealizabilityFromEventFlow
          (choiceSequenceRealizabilityToEventFlow x) =
        choiceSequenceRealizabilityFromEventFlow
          (choiceSequenceRealizabilityToEventFlow y) :=
    congrArg choiceSequenceRealizabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (choiceSequenceRealizability_round_trip x).symm
      (Eq.trans hread (choiceSequenceRealizability_round_trip y)))

instance choiceSequenceRealizabilityBHistCarrier :
    BHistCarrier ChoiceSequenceRealizabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := choiceSequenceRealizabilityToEventFlow
  fromEventFlow := choiceSequenceRealizabilityFromEventFlow

instance choiceSequenceRealizabilityChapterTasteGate :
    ChapterTasteGate ChoiceSequenceRealizabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      choiceSequenceRealizabilityFromEventFlow
          (choiceSequenceRealizabilityToEventFlow x) =
        some x
    exact choiceSequenceRealizability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (choiceSequenceRealizabilityToEventFlow_injective heq)

theorem ChoiceSequenceRealizabilityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      choiceSequenceRealizabilityDecodeBHist
        (choiceSequenceRealizabilityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ChoiceSequenceRealizabilityUp) ∧
        Nonempty (ChapterTasteGate ChoiceSequenceRealizabilityUp) ∧
          choiceSequenceRealizabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact choiceSequenceRealizabilityDecode_encode_bhist
  · constructor
    · exact ⟨choiceSequenceRealizabilityBHistCarrier⟩
    · constructor
      · exact ⟨choiceSequenceRealizabilityChapterTasteGate⟩
      · rfl

end BEDC.Derived.ChoiceSequenceRealizabilityUp
