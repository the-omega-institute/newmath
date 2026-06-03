import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffContentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffContentUp : Type where
  | mk (M A R S U B H C P N : BHist) : HausdorffContentUp
  deriving DecidableEq

def hausdorffContentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffContentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffContentEncodeBHist h

def hausdorffContentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffContentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffContentDecodeBHist tail)

private theorem HausdorffContentTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hausdorffContentDecodeBHist (hausdorffContentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def hausdorffContentFields : HausdorffContentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffContentUp.mk M A R S U B H C P N => [M, A, R, S, U, B, H, C, P, N]

def hausdorffContentToEventFlow : HausdorffContentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffContentFields x).map hausdorffContentEncodeBHist

private def hausdorffContentEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffContentEventAt index rest

def hausdorffContentFromEventFlow (ef : EventFlow) : Option HausdorffContentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffContentUp.mk
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 0 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 1 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 2 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 3 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 4 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 5 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 6 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 7 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 8 ef))
      (hausdorffContentDecodeBHist (hausdorffContentEventAt 9 ef)))

private theorem HausdorffContentTasteGate_single_carrier_alignment_round_trip
    (x : HausdorffContentUp) :
    hausdorffContentFromEventFlow (hausdorffContentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M A R S U B H C P N =>
      change
        some
          (HausdorffContentUp.mk
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist M))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist A))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist R))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist S))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist U))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist B))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist H))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist C))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist P))
            (hausdorffContentDecodeBHist (hausdorffContentEncodeBHist N))) =
          some (HausdorffContentUp.mk M A R S U B H C P N)
      rw [HausdorffContentTasteGate_single_carrier_alignment_decode_encode M,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode A,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode R,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode S,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode U,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode B,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode H,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode C,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode P,
        HausdorffContentTasteGate_single_carrier_alignment_decode_encode N]

private theorem HausdorffContentTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HausdorffContentUp} :
    hausdorffContentToEventFlow x = hausdorffContentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffContentFromEventFlow (hausdorffContentToEventFlow x) =
        hausdorffContentFromEventFlow (hausdorffContentToEventFlow y) :=
    congrArg hausdorffContentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HausdorffContentTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HausdorffContentTasteGate_single_carrier_alignment_round_trip y)))

instance hausdorffContentBHistCarrier : BHistCarrier HausdorffContentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffContentToEventFlow
  fromEventFlow := hausdorffContentFromEventFlow

instance hausdorffContentChapterTasteGate :
    ChapterTasteGate HausdorffContentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffContentFromEventFlow (hausdorffContentToEventFlow x) = some x
    exact HausdorffContentTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffContentTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem HausdorffContentTasteGate_single_carrier_alignment :
    (∀ h : BHist, hausdorffContentDecodeBHist (hausdorffContentEncodeBHist h) = h) ∧
      (∀ x : HausdorffContentUp,
        hausdorffContentFromEventFlow (hausdorffContentToEventFlow x) = some x) ∧
        (∀ x y : HausdorffContentUp,
          hausdorffContentToEventFlow x = hausdorffContentToEventFlow y → x = y) ∧
          hausdorffContentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HausdorffContentTasteGate_single_carrier_alignment_decode_encode,
      HausdorffContentTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HausdorffContentTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HausdorffContentUp
