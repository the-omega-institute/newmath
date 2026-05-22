import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionInductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionInductionUp : Type where
  | mk (Q F D R E U K H C P N : BHist) : BishopCompletionInductionUp
  deriving DecidableEq

def bishopCompletionInductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionInductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionInductionEncodeBHist h

def bishopCompletionInductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionInductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionInductionDecodeBHist tail)

private theorem bishopCompletionInduction_decode_encode_bhist :
    ∀ h : BHist,
      bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionInductionFields : BishopCompletionInductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionInductionUp.mk Q F D R E U K H C P N => [Q, F, D, R, E, U, K, H, C, P, N]

def bishopCompletionInductionToEventFlow : BishopCompletionInductionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCompletionInductionFields x).map bishopCompletionInductionEncodeBHist

private def bishopCompletionInductionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionInductionEventAtDefault index rest

def bishopCompletionInductionFromEventFlow
    (ef : EventFlow) : Option BishopCompletionInductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCompletionInductionUp.mk
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 0 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 1 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 2 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 3 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 4 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 5 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 6 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 7 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 8 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 9 ef))
      (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEventAtDefault 10 ef)))

private theorem bishopCompletionInduction_round_trip :
    ∀ x : BishopCompletionInductionUp,
      bishopCompletionInductionFromEventFlow
        (bishopCompletionInductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q F D R E U K H C P N =>
      change
        some
          (BishopCompletionInductionUp.mk
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist Q))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist F))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist D))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist R))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist E))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist U))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist K))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist H))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist C))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist P))
            (bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist N))) =
          some (BishopCompletionInductionUp.mk Q F D R E U K H C P N)
      rw [bishopCompletionInduction_decode_encode_bhist Q,
        bishopCompletionInduction_decode_encode_bhist F,
        bishopCompletionInduction_decode_encode_bhist D,
        bishopCompletionInduction_decode_encode_bhist R,
        bishopCompletionInduction_decode_encode_bhist E,
        bishopCompletionInduction_decode_encode_bhist U,
        bishopCompletionInduction_decode_encode_bhist K,
        bishopCompletionInduction_decode_encode_bhist H,
        bishopCompletionInduction_decode_encode_bhist C,
        bishopCompletionInduction_decode_encode_bhist P,
        bishopCompletionInduction_decode_encode_bhist N]

private theorem bishopCompletionInductionToEventFlow_injective
    {x y : BishopCompletionInductionUp} :
    bishopCompletionInductionToEventFlow x = bishopCompletionInductionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionInductionFromEventFlow (bishopCompletionInductionToEventFlow x) =
        bishopCompletionInductionFromEventFlow (bishopCompletionInductionToEventFlow y) :=
    congrArg bishopCompletionInductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompletionInduction_round_trip x).symm
      (Eq.trans hread (bishopCompletionInduction_round_trip y)))

instance bishopCompletionInductionBHistCarrier :
    BHistCarrier BishopCompletionInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionInductionToEventFlow
  fromEventFlow := bishopCompletionInductionFromEventFlow

instance bishopCompletionInductionChapterTasteGate :
    ChapterTasteGate BishopCompletionInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionInductionFromEventFlow
        (bishopCompletionInductionToEventFlow x) = some x
    exact bishopCompletionInduction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompletionInductionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCompletionInductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompletionInductionChapterTasteGate

theorem BishopCompletionInductionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopCompletionInductionDecodeBHist (bishopCompletionInductionEncodeBHist h) = h) ∧
      (∀ x : BishopCompletionInductionUp,
        bishopCompletionInductionFromEventFlow (bishopCompletionInductionToEventFlow x) = some x) ∧
      (∀ x y : BishopCompletionInductionUp,
        bishopCompletionInductionToEventFlow x = bishopCompletionInductionToEventFlow y → x = y) ∧
      bishopCompletionInductionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bishopCompletionInduction_decode_encode_bhist,
      bishopCompletionInduction_round_trip,
      (fun _ _ heq => bishopCompletionInductionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopCompletionInductionUp
