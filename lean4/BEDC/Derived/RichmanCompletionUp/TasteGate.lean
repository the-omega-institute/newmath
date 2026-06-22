import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RichmanCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RichmanCompletionUp : Type where
  | mk (D S Q E L B H C P N : BHist) : RichmanCompletionUp
  deriving DecidableEq

def richmanCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: richmanCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: richmanCompletionEncodeBHist h

def richmanCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (richmanCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (richmanCompletionDecodeBHist tail)

private theorem richmanCompletion_decode_encode :
    ∀ h : BHist, richmanCompletionDecodeBHist
      (richmanCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def richmanCompletionFields : RichmanCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RichmanCompletionUp.mk D S Q E L B H C P N => [D, S, Q, E, L, B, H, C, P, N]

def richmanCompletionToEventFlow : RichmanCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (richmanCompletionFields x).map richmanCompletionEncodeBHist

private def richmanCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => richmanCompletionRawAt index rest

private def richmanCompletionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => richmanCompletionLengthEq index rest

def richmanCompletionFromEventFlow : EventFlow → Option RichmanCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match richmanCompletionLengthEq 10 flow with
      | true =>
          some
            (RichmanCompletionUp.mk
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 0 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 1 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 2 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 3 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 4 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 5 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 6 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 7 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 8 flow))
              (richmanCompletionDecodeBHist (richmanCompletionRawAt 9 flow)))
      | false => none

private theorem richmanCompletion_round_trip :
    ∀ x : RichmanCompletionUp,
      richmanCompletionFromEventFlow (richmanCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S Q E L B H C P N =>
      change
        some
          (RichmanCompletionUp.mk
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist D))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist S))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist Q))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist E))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist L))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist B))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist H))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist C))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist P))
            (richmanCompletionDecodeBHist (richmanCompletionEncodeBHist N))) =
          some (RichmanCompletionUp.mk D S Q E L B H C P N)
      rw [richmanCompletion_decode_encode D,
        richmanCompletion_decode_encode S,
        richmanCompletion_decode_encode Q,
        richmanCompletion_decode_encode E,
        richmanCompletion_decode_encode L,
        richmanCompletion_decode_encode B,
        richmanCompletion_decode_encode H,
        richmanCompletion_decode_encode C,
        richmanCompletion_decode_encode P,
        richmanCompletion_decode_encode N]

private theorem richmanCompletionToEventFlow_injective
    {x y : RichmanCompletionUp} :
    richmanCompletionToEventFlow x = richmanCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      richmanCompletionFromEventFlow (richmanCompletionToEventFlow x) =
        richmanCompletionFromEventFlow (richmanCompletionToEventFlow y) :=
    congrArg richmanCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (richmanCompletion_round_trip x).symm
      (Eq.trans hread (richmanCompletion_round_trip y)))

instance richmanCompletionBHistCarrier :
    BHistCarrier RichmanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := richmanCompletionToEventFlow
  fromEventFlow := richmanCompletionFromEventFlow

instance richmanCompletionChapterTasteGate :
    ChapterTasteGate RichmanCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      richmanCompletionFromEventFlow (richmanCompletionToEventFlow x) =
        some x
    exact richmanCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (richmanCompletionToEventFlow_injective heq)

theorem RichmanCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, richmanCompletionDecodeBHist
      (richmanCompletionEncodeBHist h) = h) ∧
      (∀ x : RichmanCompletionUp,
        richmanCompletionFromEventFlow
          (richmanCompletionToEventFlow x) = some x) ∧
        (∀ x y : RichmanCompletionUp,
          richmanCompletionToEventFlow x =
            richmanCompletionToEventFlow y → x = y) ∧
          richmanCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact richmanCompletion_decode_encode
  · constructor
    · exact richmanCompletion_round_trip
    · constructor
      · intro x y heq
        exact richmanCompletionToEventFlow_injective heq
      · rfl

end BEDC.Derived.RichmanCompletionUp
