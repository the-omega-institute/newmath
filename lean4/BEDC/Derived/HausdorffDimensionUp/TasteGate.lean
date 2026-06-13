import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffDimensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffDimensionUp : Type where
  | mk (M K G C W R S D T P N : BHist) : HausdorffDimensionUp
  deriving DecidableEq

def hausdorffDimensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffDimensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffDimensionEncodeBHist h

def hausdorffDimensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffDimensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffDimensionDecodeBHist tail)

theorem HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffDimensionFields : HausdorffDimensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffDimensionUp.mk M K G C W R S D T P N => [M, K, G, C, W, R, S, D, T, P, N]

def hausdorffDimensionToEventFlow : HausdorffDimensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffDimensionFields x).map hausdorffDimensionEncodeBHist

private def hausdorffDimensionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffDimensionEventAt index rest

def hausdorffDimensionFromEventFlow (ef : EventFlow) : Option HausdorffDimensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffDimensionUp.mk
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 0 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 1 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 2 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 3 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 4 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 5 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 6 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 7 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 8 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 9 ef))
      (hausdorffDimensionDecodeBHist (hausdorffDimensionEventAt 10 ef)))

theorem HausdorffDimensionTasteGate_single_carrier_alignment_round_trip
    (x : HausdorffDimensionUp) :
    hausdorffDimensionFromEventFlow (hausdorffDimensionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M K G C W R S D T P N =>
      change
        some
          (HausdorffDimensionUp.mk
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist M))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist K))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist G))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist C))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist W))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist R))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist S))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist D))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist T))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist P))
            (hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist N))) =
          some (HausdorffDimensionUp.mk M K G C W R S D T P N)
      rw [HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode M,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode K,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode G,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode C,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode W,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode R,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode S,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode D,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode T,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode P,
        HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode N]

theorem HausdorffDimensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HausdorffDimensionUp} :
    hausdorffDimensionToEventFlow x = hausdorffDimensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = hausdorffDimensionFromEventFlow (hausdorffDimensionToEventFlow x) :=
        (HausdorffDimensionTasteGate_single_carrier_alignment_round_trip x).symm
      _ = hausdorffDimensionFromEventFlow (hausdorffDimensionToEventFlow y) :=
        congrArg hausdorffDimensionFromEventFlow hxy
      _ = some y := HausdorffDimensionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance hausdorffDimensionBHistCarrier : BHistCarrier HausdorffDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffDimensionToEventFlow
  fromEventFlow := hausdorffDimensionFromEventFlow

instance hausdorffDimensionChapterTasteGate :
    ChapterTasteGate HausdorffDimensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffDimensionFromEventFlow (hausdorffDimensionToEventFlow x) = some x
    exact HausdorffDimensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffDimensionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HausdorffDimensionTasteGate_single_carrier_alignment :
    (∀ h : BHist, hausdorffDimensionDecodeBHist (hausdorffDimensionEncodeBHist h) = h) ∧
      (∀ x : HausdorffDimensionUp,
        hausdorffDimensionFromEventFlow (hausdorffDimensionToEventFlow x) = some x) ∧
        (∀ x y : HausdorffDimensionUp,
          hausdorffDimensionToEventFlow x = hausdorffDimensionToEventFlow y → x = y) ∧
          hausdorffDimensionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HausdorffDimensionTasteGate_single_carrier_alignment_decode_encode,
      HausdorffDimensionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HausdorffDimensionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HausdorffDimensionUp
