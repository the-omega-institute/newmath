import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyCriterionUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyCriterionUp : Type where
  | mk (D S R E K H C P N : BHist) : BishopCauchyCriterionUp
  deriving DecidableEq

def bishopCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyCriterionEncodeBHist h

def bishopCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyCriterionDecodeBHist tail)

private theorem BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyCriterionFields : BishopCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyCriterionUp.mk D S R E K H C P N => [D, S, R, E, K, H, C, P, N]

def bishopCauchyCriterionToEventFlow : BishopCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopCauchyCriterionFields x).map bishopCauchyCriterionEncodeBHist

private def bishopCauchyCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyCriterionEventAt index rest

def bishopCauchyCriterionFromEventFlow (ef : EventFlow) :
    Option BishopCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyCriterionUp.mk
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 0 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 1 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 2 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 3 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 4 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 5 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 6 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 7 ef))
      (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEventAt 8 ef)))

private theorem BishopCauchyCriterionTasteGate_single_carrier_alignment_round_trip
    (x : BishopCauchyCriterionUp) :
    bishopCauchyCriterionFromEventFlow (bishopCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R E K H C P N =>
      change
        some
          (BishopCauchyCriterionUp.mk
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist D))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist S))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist R))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist E))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist K))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist H))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist C))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist P))
            (bishopCauchyCriterionDecodeBHist (bishopCauchyCriterionEncodeBHist N))) =
          some (BishopCauchyCriterionUp.mk D S R E K H C P N)
      rw [BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode D,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode S,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode R,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode E,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode K,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode H,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode C,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode P,
        BishopCauchyCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCauchyCriterionUp} :
    bishopCauchyCriterionToEventFlow x = bishopCauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyCriterionFromEventFlow (bishopCauchyCriterionToEventFlow x) =
        bishopCauchyCriterionFromEventFlow (bishopCauchyCriterionToEventFlow y) :=
    congrArg bishopCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCauchyCriterionBHistCarrier : BHistCarrier BishopCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyCriterionToEventFlow
  fromEventFlow := bishopCauchyCriterionFromEventFlow

instance bishopCauchyCriterionChapterTasteGate :
    ChapterTasteGate BishopCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCauchyCriterionFromEventFlow
      (bishopCauchyCriterionToEventFlow x) = some x
    exact BishopCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopCauchyCriterionTasteGate_single_carrier_alignment :
    bishopCauchyCriterionDecodeBHist
        (bishopCauchyCriterionEncodeBHist BHist.Empty) = BHist.Empty ∧
      (forall x : BishopCauchyCriterionUp,
        bishopCauchyCriterionFromEventFlow (bishopCauchyCriterionToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · exact BishopCauchyCriterionTasteGate_single_carrier_alignment_round_trip

end TasteGate
end BEDC.Derived.BishopCauchyCriterionUp
