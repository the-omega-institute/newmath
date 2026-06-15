import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffRealCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffRealCompletionUp : Type where
  | mk (A U S D R E H C P N : BHist) : HausdorffRealCompletionUp
  deriving DecidableEq

def hausdorffRealCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffRealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffRealCompletionEncodeBHist h

def hausdorffRealCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffRealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffRealCompletionDecodeBHist tail)

theorem HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffRealCompletionFields : HausdorffRealCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffRealCompletionUp.mk A U S D R E H C P N => [A, U, S, D, R, E, H, C, P, N]

def hausdorffRealCompletionToEventFlow : HausdorffRealCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffRealCompletionFields x).map hausdorffRealCompletionEncodeBHist

private def hausdorffRealCompletionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffRealCompletionEventAt index rest

def hausdorffRealCompletionFromEventFlow (ef : EventFlow) : Option HausdorffRealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffRealCompletionUp.mk
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 0 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 1 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 2 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 3 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 4 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 5 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 6 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 7 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 8 ef))
      (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEventAt 9 ef)))

theorem HausdorffRealCompletionTasteGate_single_carrier_alignment_round_trip
    (x : HausdorffRealCompletionUp) :
    hausdorffRealCompletionFromEventFlow (hausdorffRealCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A U S D R E H C P N =>
      change
        some
          (HausdorffRealCompletionUp.mk
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist A))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist U))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist S))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist D))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist R))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist E))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist H))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist C))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist P))
            (hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist N))) =
          some (HausdorffRealCompletionUp.mk A U S D R E H C P N)
      rw [HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode A,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode U,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode S,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode D,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode R,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode E,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode H,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode C,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode P,
        HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode N]

theorem HausdorffRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HausdorffRealCompletionUp} :
    hausdorffRealCompletionToEventFlow x = hausdorffRealCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = hausdorffRealCompletionFromEventFlow (hausdorffRealCompletionToEventFlow x) :=
        (HausdorffRealCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      _ = hausdorffRealCompletionFromEventFlow (hausdorffRealCompletionToEventFlow y) :=
        congrArg hausdorffRealCompletionFromEventFlow hxy
      _ = some y := HausdorffRealCompletionTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance hausdorffRealCompletionBHistCarrier :
    BHistCarrier HausdorffRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffRealCompletionToEventFlow
  fromEventFlow := hausdorffRealCompletionFromEventFlow

instance hausdorffRealCompletionChapterTasteGate :
    ChapterTasteGate HausdorffRealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffRealCompletionFromEventFlow (hausdorffRealCompletionToEventFlow x) = some x
    exact HausdorffRealCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HausdorffRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HausdorffRealCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hausdorffRealCompletionDecodeBHist (hausdorffRealCompletionEncodeBHist h) = h) ∧
      (∀ x : HausdorffRealCompletionUp,
        hausdorffRealCompletionFromEventFlow (hausdorffRealCompletionToEventFlow x) = some x) ∧
        (∀ x y : HausdorffRealCompletionUp,
          hausdorffRealCompletionToEventFlow x = hausdorffRealCompletionToEventFlow y → x = y) ∧
          hausdorffRealCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HausdorffRealCompletionTasteGate_single_carrier_alignment_decode_encode,
      HausdorffRealCompletionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HausdorffRealCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HausdorffRealCompletionUp
