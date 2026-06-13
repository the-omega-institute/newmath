import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopMetricCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopMetricCompletionUp : Type where
  | mk (M E Q W S R T H C P N : BHist) : BishopMetricCompletionUp
  deriving DecidableEq

def bishopMetricCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopMetricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopMetricCompletionEncodeBHist h

def bishopMetricCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopMetricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopMetricCompletionDecodeBHist tail)

private theorem BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopMetricCompletionFields : BishopMetricCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopMetricCompletionUp.mk M E Q W S R T H C P N => [M, E, Q, W, S, R, T, H, C, P, N]

def bishopMetricCompletionToEventFlow : BishopMetricCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopMetricCompletionFields x).map bishopMetricCompletionEncodeBHist

private def bishopMetricCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopMetricCompletionEventAtDefault index rest

def bishopMetricCompletionFromEventFlow (ef : EventFlow) : Option BishopMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopMetricCompletionUp.mk
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 0 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 1 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 2 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 3 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 4 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 5 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 6 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 7 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 8 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 9 ef))
      (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEventAtDefault 10 ef)))

private theorem BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopMetricCompletionUp,
      bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E Q W S R T H C P N =>
      change
        some
          (BishopMetricCompletionUp.mk
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist M))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist E))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist Q))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist W))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist S))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist R))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist T))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist H))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist C))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist P))
            (bishopMetricCompletionDecodeBHist (bishopMetricCompletionEncodeBHist N))) =
          some (BishopMetricCompletionUp.mk M E Q W S R T H C P N)
      rw [BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode M,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode Q,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode W,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode T,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopMetricCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopMetricCompletionUp} :
    bishopMetricCompletionToEventFlow x = bishopMetricCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow x) =
        bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow y) :=
    congrArg bishopMetricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopMetricCompletionBHistCarrier : BHistCarrier BishopMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopMetricCompletionToEventFlow
  fromEventFlow := bishopMetricCompletionFromEventFlow

instance bishopMetricCompletionChapterTasteGate :
    ChapterTasteGate BishopMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopMetricCompletionFromEventFlow (bishopMetricCompletionToEventFlow x) = some x
    exact BishopMetricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopMetricCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopMetricCompletionTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BishopMetricCompletionUp) ∧
      Nonempty (ChapterTasteGate BishopMetricCompletionUp) ∧
        bishopMetricCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨bishopMetricCompletionBHistCarrier⟩
  constructor
  · exact ⟨bishopMetricCompletionChapterTasteGate⟩
  · rfl

end BEDC.Derived.BishopMetricCompletionUp
