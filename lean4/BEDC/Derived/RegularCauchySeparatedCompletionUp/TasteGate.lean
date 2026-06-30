import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySeparatedCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySeparatedCompletionUp : Type where
  | mk (R S D Z E H C P N : BHist) : RegularCauchySeparatedCompletionUp
  deriving DecidableEq

def regularCauchySeparatedCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySeparatedCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySeparatedCompletionEncodeBHist h

def regularCauchySeparatedCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySeparatedCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySeparatedCompletionDecodeBHist tail)

private theorem regularCauchySeparatedCompletion_decode_encode :
    ∀ h : BHist,
      regularCauchySeparatedCompletionDecodeBHist
          (regularCauchySeparatedCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySeparatedCompletionToEventFlow :
    RegularCauchySeparatedCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySeparatedCompletionUp.mk R S D Z E H C P N =>
      [regularCauchySeparatedCompletionEncodeBHist R,
        regularCauchySeparatedCompletionEncodeBHist S,
        regularCauchySeparatedCompletionEncodeBHist D,
        regularCauchySeparatedCompletionEncodeBHist Z,
        regularCauchySeparatedCompletionEncodeBHist E,
        regularCauchySeparatedCompletionEncodeBHist H,
        regularCauchySeparatedCompletionEncodeBHist C,
        regularCauchySeparatedCompletionEncodeBHist P,
        regularCauchySeparatedCompletionEncodeBHist N]

def regularCauchySeparatedCompletionFromEventFlow
    (flow : EventFlow) : Option RegularCauchySeparatedCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | R :: rest =>
      match rest with
      | [] => none
      | S :: rest =>
          match rest with
          | [] => none
          | D :: rest =>
              match rest with
              | [] => none
              | Z :: rest =>
                  match rest with
                  | [] => none
                  | E :: rest =>
                      match rest with
                      | [] => none
                      | H :: rest =>
                          match rest with
                          | [] => none
                          | C :: rest =>
                              match rest with
                              | [] => none
                              | P :: rest =>
                                  match rest with
                                  | [] => none
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (RegularCauchySeparatedCompletionUp.mk
                                              (regularCauchySeparatedCompletionDecodeBHist R)
                                              (regularCauchySeparatedCompletionDecodeBHist S)
                                              (regularCauchySeparatedCompletionDecodeBHist D)
                                              (regularCauchySeparatedCompletionDecodeBHist Z)
                                              (regularCauchySeparatedCompletionDecodeBHist E)
                                              (regularCauchySeparatedCompletionDecodeBHist H)
                                              (regularCauchySeparatedCompletionDecodeBHist C)
                                              (regularCauchySeparatedCompletionDecodeBHist P)
                                              (regularCauchySeparatedCompletionDecodeBHist N))
                                      | _ :: _ => none

private theorem regularCauchySeparatedCompletion_round_trip :
    ∀ x : RegularCauchySeparatedCompletionUp,
      regularCauchySeparatedCompletionFromEventFlow
          (regularCauchySeparatedCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D Z E H C P N =>
      rw [regularCauchySeparatedCompletionToEventFlow,
        regularCauchySeparatedCompletionFromEventFlow,
        regularCauchySeparatedCompletion_decode_encode R,
        regularCauchySeparatedCompletion_decode_encode S,
        regularCauchySeparatedCompletion_decode_encode D,
        regularCauchySeparatedCompletion_decode_encode Z,
        regularCauchySeparatedCompletion_decode_encode E,
        regularCauchySeparatedCompletion_decode_encode H,
        regularCauchySeparatedCompletion_decode_encode C,
        regularCauchySeparatedCompletion_decode_encode P,
        regularCauchySeparatedCompletion_decode_encode N]

private theorem regularCauchySeparatedCompletionToEventFlow_injective
    {x y : RegularCauchySeparatedCompletionUp} :
    regularCauchySeparatedCompletionToEventFlow x =
        regularCauchySeparatedCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySeparatedCompletionFromEventFlow
          (regularCauchySeparatedCompletionToEventFlow x) =
        regularCauchySeparatedCompletionFromEventFlow
          (regularCauchySeparatedCompletionToEventFlow y) :=
    congrArg regularCauchySeparatedCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySeparatedCompletion_round_trip x).symm
      (Eq.trans hread (regularCauchySeparatedCompletion_round_trip y)))

instance regularCauchySeparatedCompletionBHistCarrier :
    BHistCarrier RegularCauchySeparatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySeparatedCompletionToEventFlow
  fromEventFlow := regularCauchySeparatedCompletionFromEventFlow

instance regularCauchySeparatedCompletionChapterTasteGate :
    ChapterTasteGate RegularCauchySeparatedCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySeparatedCompletionFromEventFlow
          (regularCauchySeparatedCompletionToEventFlow x) =
        some x
    exact regularCauchySeparatedCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySeparatedCompletionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySeparatedCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySeparatedCompletionChapterTasteGate

theorem RegularCauchySeparatedCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySeparatedCompletionDecodeBHist
          (regularCauchySeparatedCompletionEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchySeparatedCompletionUp,
        regularCauchySeparatedCompletionFromEventFlow
            (regularCauchySeparatedCompletionToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchySeparatedCompletionUp,
        regularCauchySeparatedCompletionToEventFlow x =
            regularCauchySeparatedCompletionToEventFlow y →
          x = y) ∧
      regularCauchySeparatedCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchySeparatedCompletion_decode_encode,
      regularCauchySeparatedCompletion_round_trip,
      fun _ _ heq => regularCauchySeparatedCompletionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchySeparatedCompletionUp
