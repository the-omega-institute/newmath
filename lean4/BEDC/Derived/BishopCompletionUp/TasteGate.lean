import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionUp : Type where
  | mk (R S D E F U H C P N : BHist) : BishopCompletionUp
  deriving DecidableEq

def bishopCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionEncodeBHist h

def bishopCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionDecodeBHist tail)

private theorem bishopCompletionDecode_encode_bhist :
    ∀ h : BHist, bishopCompletionDecodeBHist (bishopCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionFields : BishopCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionUp.mk R S D E F U H C P N => [R, S, D, E, F, U, H, C, P, N]

def bishopCompletionToEventFlow : BishopCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCompletionFields x).map bishopCompletionEncodeBHist

private def bishopCompletionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionRawAt index rest

private def bishopCompletionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => bishopCompletionLengthEq index rest

def bishopCompletionFromEventFlow : EventFlow → Option BishopCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match bishopCompletionLengthEq 10 flow with
      | true =>
          some
            (BishopCompletionUp.mk
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 0 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 1 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 2 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 3 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 4 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 5 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 6 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 7 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 8 flow))
              (bishopCompletionDecodeBHist (bishopCompletionRawAt 9 flow)))
      | false => none

private theorem bishopCompletion_round_trip :
    ∀ x : BishopCompletionUp,
      bishopCompletionFromEventFlow (bishopCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S D E F U H C P N =>
      change
        some
          (BishopCompletionUp.mk
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist R))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist S))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist D))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist E))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist F))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist U))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist H))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist C))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist P))
            (bishopCompletionDecodeBHist (bishopCompletionEncodeBHist N))) =
          some (BishopCompletionUp.mk R S D E F U H C P N)
      rw [bishopCompletionDecode_encode_bhist R, bishopCompletionDecode_encode_bhist S,
        bishopCompletionDecode_encode_bhist D, bishopCompletionDecode_encode_bhist E,
        bishopCompletionDecode_encode_bhist F, bishopCompletionDecode_encode_bhist U,
        bishopCompletionDecode_encode_bhist H, bishopCompletionDecode_encode_bhist C,
        bishopCompletionDecode_encode_bhist P, bishopCompletionDecode_encode_bhist N]

private theorem bishopCompletionToEventFlow_injective {x y : BishopCompletionUp} :
    bishopCompletionToEventFlow x = bishopCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionFromEventFlow (bishopCompletionToEventFlow x) =
        bishopCompletionFromEventFlow (bishopCompletionToEventFlow y) :=
    congrArg bishopCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompletion_round_trip x).symm
      (Eq.trans hread (bishopCompletion_round_trip y)))

instance bishopCompletionBHistCarrier : BHistCarrier BishopCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionToEventFlow
  fromEventFlow := bishopCompletionFromEventFlow

instance bishopCompletionChapterTasteGate : ChapterTasteGate BishopCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompletionFromEventFlow (bishopCompletionToEventFlow x) = some x
    exact bishopCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompletionToEventFlow_injective heq)

theorem BishopCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCompletionDecodeBHist (bishopCompletionEncodeBHist h) = h) ∧
      bishopCompletionFromEventFlow
          (bishopCompletionToEventFlow
            (BishopCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
        some
          (BishopCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact bishopCompletionDecode_encode_bhist
  · exact bishopCompletion_round_trip
      (BishopCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)

end BEDC.Derived.BishopCompletionUp
