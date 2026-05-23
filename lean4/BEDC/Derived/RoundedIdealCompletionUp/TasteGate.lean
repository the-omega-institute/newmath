import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RoundedIdealCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RoundedIdealCompletionUp : Type where
  | mk (M F D S R E T C P N : BHist) : RoundedIdealCompletionUp
  deriving DecidableEq

def roundedIdealCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: roundedIdealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: roundedIdealCompletionEncodeBHist h

def roundedIdealCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (roundedIdealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (roundedIdealCompletionDecodeBHist tail)

private theorem roundedIdealCompletionDecode_encode_bhist :
    ∀ h : BHist,
      roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def roundedIdealCompletionFields : RoundedIdealCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RoundedIdealCompletionUp.mk M F D S R E T C P N => [M, F, D, S, R, E, T, C, P, N]

def roundedIdealCompletionToEventFlow : RoundedIdealCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (roundedIdealCompletionFields x).map roundedIdealCompletionEncodeBHist

def roundedIdealCompletionFromEventFlow : EventFlow → Option RoundedIdealCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: restF =>
      match restF with
      | [] => none
      | F :: restD =>
          match restD with
          | [] => none
          | D :: restS =>
              match restS with
              | [] => none
              | S :: restR =>
                  match restR with
                  | [] => none
                  | R :: restE =>
                      match restE with
                      | [] => none
                      | E :: restT =>
                          match restT with
                          | [] => none
                          | T :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (RoundedIdealCompletionUp.mk
                                                  (roundedIdealCompletionDecodeBHist M)
                                                  (roundedIdealCompletionDecodeBHist F)
                                                  (roundedIdealCompletionDecodeBHist D)
                                                  (roundedIdealCompletionDecodeBHist S)
                                                  (roundedIdealCompletionDecodeBHist R)
                                                  (roundedIdealCompletionDecodeBHist E)
                                                  (roundedIdealCompletionDecodeBHist T)
                                                  (roundedIdealCompletionDecodeBHist C)
                                                  (roundedIdealCompletionDecodeBHist P)
                                                  (roundedIdealCompletionDecodeBHist N))
                                          | _ :: _ => none

private theorem roundedIdealCompletion_round_trip :
    ∀ x : RoundedIdealCompletionUp,
      roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F D S R E T C P N =>
      change
        some
          (RoundedIdealCompletionUp.mk
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist M))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist F))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist D))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist S))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist R))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist E))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist T))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist C))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist P))
            (roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist N))) =
          some (RoundedIdealCompletionUp.mk M F D S R E T C P N)
      rw [roundedIdealCompletionDecode_encode_bhist M,
        roundedIdealCompletionDecode_encode_bhist F,
        roundedIdealCompletionDecode_encode_bhist D,
        roundedIdealCompletionDecode_encode_bhist S,
        roundedIdealCompletionDecode_encode_bhist R,
        roundedIdealCompletionDecode_encode_bhist E,
        roundedIdealCompletionDecode_encode_bhist T,
        roundedIdealCompletionDecode_encode_bhist C,
        roundedIdealCompletionDecode_encode_bhist P,
        roundedIdealCompletionDecode_encode_bhist N]

private theorem roundedIdealCompletionToEventFlow_injective
    {x y : RoundedIdealCompletionUp} :
    roundedIdealCompletionToEventFlow x = roundedIdealCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow x) =
        roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow y) :=
    congrArg roundedIdealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (roundedIdealCompletion_round_trip x).symm
      (Eq.trans hread (roundedIdealCompletion_round_trip y)))

private theorem roundedIdealCompletionFields_faithful :
    ∀ x y : RoundedIdealCompletionUp,
      roundedIdealCompletionFields x = roundedIdealCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk M1 F1 D1 S1 R1 E1 T1 C1 P1 N1 =>
      cases y with
      | mk M2 F2 D2 S2 R2 E2 T2 C2 P2 N2 =>
          cases h
          rfl

instance roundedIdealCompletionBHistCarrier :
    BHistCarrier RoundedIdealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := roundedIdealCompletionToEventFlow
  fromEventFlow := roundedIdealCompletionFromEventFlow

instance roundedIdealCompletionChapterTasteGate :
    ChapterTasteGate RoundedIdealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow x) = some x
    exact roundedIdealCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (roundedIdealCompletionToEventFlow_injective heq)

instance roundedIdealCompletionFieldFaithful :
    FieldFaithful RoundedIdealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := roundedIdealCompletionFields
  field_faithful := roundedIdealCompletionFields_faithful

instance roundedIdealCompletionNontrivial : Nontrivial RoundedIdealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RoundedIdealCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RoundedIdealCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RoundedIdealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  roundedIdealCompletionChapterTasteGate

namespace TasteGate

theorem RoundedIdealCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RoundedIdealCompletionUp) ∧
      Nonempty (FieldFaithful RoundedIdealCompletionUp) ∧
        Nonempty (Nontrivial RoundedIdealCompletionUp) ∧
          (∀ h : BHist,
            roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist h) = h) ∧
            (∀ x : RoundedIdealCompletionUp,
              roundedIdealCompletionFromEventFlow
                (roundedIdealCompletionToEventFlow x) = some x) ∧
              (∀ x y : RoundedIdealCompletionUp,
                roundedIdealCompletionToEventFlow x =
                    roundedIdealCompletionToEventFlow y →
                  x = y) ∧
                roundedIdealCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨roundedIdealCompletionChapterTasteGate⟩
  · constructor
    · exact ⟨roundedIdealCompletionFieldFaithful⟩
    · constructor
      · exact ⟨roundedIdealCompletionNontrivial⟩
      · constructor
        · exact roundedIdealCompletionDecode_encode_bhist
        · constructor
          · exact roundedIdealCompletion_round_trip
          · constructor
            · intro x y heq
              exact roundedIdealCompletionToEventFlow_injective heq
            · rfl

def taste_gate : ChapterTasteGate RoundedIdealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.RoundedIdealCompletionUp.taste_gate

end TasteGate

end BEDC.Derived.RoundedIdealCompletionUp
