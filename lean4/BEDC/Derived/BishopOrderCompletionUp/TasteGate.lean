import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopOrderCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopOrderCompletionUp : Type where
  | mk (D S R E B L U H C P N : BHist) : BishopOrderCompletionUp
  deriving DecidableEq

def bishopOrderCompletionEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopOrderCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopOrderCompletionEncodeBHist h

def bishopOrderCompletionDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopOrderCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopOrderCompletionDecodeBHist tail)

private theorem bishopOrderCompletion_decode_encode :
    ∀ h : BHist,
      bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopOrderCompletionFields : BishopOrderCompletionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BishopOrderCompletionUp.mk D S R E B L U H C P N => [D, S, R, E, B, L, U, H, C, P, N]

def bishopOrderCompletionToEventFlow : BishopOrderCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BishopOrderCompletionUp.mk D S R E B L U H C P N =>
      [bishopOrderCompletionEncodeBHist D,
        bishopOrderCompletionEncodeBHist S,
        bishopOrderCompletionEncodeBHist R,
        bishopOrderCompletionEncodeBHist E,
        bishopOrderCompletionEncodeBHist B,
        bishopOrderCompletionEncodeBHist L,
        bishopOrderCompletionEncodeBHist U,
        bishopOrderCompletionEncodeBHist H,
        bishopOrderCompletionEncodeBHist C,
        bishopOrderCompletionEncodeBHist P,
        bishopOrderCompletionEncodeBHist N]

private def bishopOrderCompletionEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopOrderCompletionEventAt index rest

def bishopOrderCompletionFromEventFlow :
    EventFlow → Option BishopOrderCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BishopOrderCompletionUp.mk
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 0 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 1 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 2 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 3 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 4 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 5 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 6 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 7 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 8 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 9 ef))
        (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEventAt 10 ef)))

private theorem bishopOrderCompletion_round_trip :
    ∀ x : BishopOrderCompletionUp,
      bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E B L U H C P N =>
      change
        some
          (BishopOrderCompletionUp.mk
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist D))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist S))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist R))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist E))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist B))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist L))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist U))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist H))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist C))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist P))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist N))) =
          some (BishopOrderCompletionUp.mk D S R E B L U H C P N)
      rw [bishopOrderCompletion_decode_encode D, bishopOrderCompletion_decode_encode S,
        bishopOrderCompletion_decode_encode R, bishopOrderCompletion_decode_encode E,
        bishopOrderCompletion_decode_encode B, bishopOrderCompletion_decode_encode L,
        bishopOrderCompletion_decode_encode U, bishopOrderCompletion_decode_encode H,
        bishopOrderCompletion_decode_encode C, bishopOrderCompletion_decode_encode P,
        bishopOrderCompletion_decode_encode N]

private theorem bishopOrderCompletionToEventFlow_injective
    {x y : BishopOrderCompletionUp} :
    bishopOrderCompletionToEventFlow x = bishopOrderCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow x) :=
        (bishopOrderCompletion_round_trip x).symm
      _ = bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow y) :=
        congrArg bishopOrderCompletionFromEventFlow hxy
      _ = some y := bishopOrderCompletion_round_trip y
  exact Option.some.inj hsome

instance bishopOrderCompletionBHistCarrier :
    BHistCarrier BishopOrderCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopOrderCompletionToEventFlow
  fromEventFlow := bishopOrderCompletionFromEventFlow

instance bishopOrderCompletionChapterTasteGate :
    ChapterTasteGate BishopOrderCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow x) = some x
    exact bishopOrderCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopOrderCompletionToEventFlow_injective heq)

theorem BishopOrderCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist h) = h) ∧
      (∀ x : BishopOrderCompletionUp,
        bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow x) = some x) ∧
      (∀ x y : BishopOrderCompletionUp,
        bishopOrderCompletionToEventFlow x = bishopOrderCompletionToEventFlow y → x = y) ∧
      bishopOrderCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bishopOrderCompletion_decode_encode, bishopOrderCompletion_round_trip,
      fun _ _ hxy => bishopOrderCompletionToEventFlow_injective hxy, rfl⟩

end BEDC.Derived.BishopOrderCompletionUp.TasteGate
