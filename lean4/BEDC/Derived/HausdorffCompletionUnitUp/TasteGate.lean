import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffCompletionUnitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffCompletionUnitUp : Type where
  | mk (M S J W R E H C P N : BHist) : HausdorffCompletionUnitUp
  deriving DecidableEq

def hausdorffCompletionUnitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionUnitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionUnitEncodeBHist h

def hausdorffCompletionUnitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionUnitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionUnitDecodeBHist tail)

private theorem hausdorffCompletionUnit_decode_encode_bhist :
    ∀ h : BHist, hausdorffCompletionUnitDecodeBHist
      (hausdorffCompletionUnitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hausdorffCompletionUnitToEventFlow : HausdorffCompletionUnitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionUnitUp.mk M S J W R E H C P N =>
      [[BMark.b0],
        hausdorffCompletionUnitEncodeBHist M,
        [BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hausdorffCompletionUnitEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        hausdorffCompletionUnitEncodeBHist N]

private def hausdorffCompletionUnitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffCompletionUnitEventAt index rest

def hausdorffCompletionUnitFromEventFlow
    (ef : EventFlow) : Option HausdorffCompletionUnitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffCompletionUnitUp.mk
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 1 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 3 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 5 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 7 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 9 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 11 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 13 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 15 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 17 ef))
      (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEventAt 19 ef)))

private theorem hausdorffCompletionUnit_round_trip :
    ∀ x : HausdorffCompletionUnitUp,
      hausdorffCompletionUnitFromEventFlow
        (hausdorffCompletionUnitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S J W R E H C P N =>
      change
        some
          (HausdorffCompletionUnitUp.mk
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist M))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist S))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist J))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist W))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist R))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist E))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist H))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist C))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist P))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist N))) =
          some (HausdorffCompletionUnitUp.mk M S J W R E H C P N)
      rw [hausdorffCompletionUnit_decode_encode_bhist M,
        hausdorffCompletionUnit_decode_encode_bhist S,
        hausdorffCompletionUnit_decode_encode_bhist J,
        hausdorffCompletionUnit_decode_encode_bhist W,
        hausdorffCompletionUnit_decode_encode_bhist R,
        hausdorffCompletionUnit_decode_encode_bhist E,
        hausdorffCompletionUnit_decode_encode_bhist H,
        hausdorffCompletionUnit_decode_encode_bhist C,
        hausdorffCompletionUnit_decode_encode_bhist P,
        hausdorffCompletionUnit_decode_encode_bhist N]

private theorem hausdorffCompletionUnitToEventFlow_injective
    {x y : HausdorffCompletionUnitUp} :
    hausdorffCompletionUnitToEventFlow x = hausdorffCompletionUnitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow x) =
        hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow y) :=
    congrArg hausdorffCompletionUnitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hausdorffCompletionUnit_round_trip x).symm
      (Eq.trans hread (hausdorffCompletionUnit_round_trip y)))

instance hausdorffCompletionUnitBHistCarrier :
    BHistCarrier HausdorffCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionUnitToEventFlow
  fromEventFlow := hausdorffCompletionUnitFromEventFlow

instance hausdorffCompletionUnitChapterTasteGate :
    ChapterTasteGate HausdorffCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow x) =
        some x
    exact hausdorffCompletionUnit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hausdorffCompletionUnitToEventFlow_injective heq)

theorem HausdorffCompletionUnitTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier HausdorffCompletionUnitUp,
        Nonempty (@ChapterTasteGate HausdorffCompletionUnitUp carrier)) ∧
      (∀ h : BHist,
        hausdorffCompletionUnitDecodeBHist
          (hausdorffCompletionUnitEncodeBHist h) = h) ∧
      (∀ x : HausdorffCompletionUnitUp,
        hausdorffCompletionUnitFromEventFlow
          (hausdorffCompletionUnitToEventFlow x) = some x) ∧
      hausdorffCompletionUnitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨hausdorffCompletionUnitBHistCarrier, ⟨hausdorffCompletionUnitChapterTasteGate⟩⟩
  · constructor
    · exact hausdorffCompletionUnit_decode_encode_bhist
    · constructor
      · exact hausdorffCompletionUnit_round_trip
      · rfl

end BEDC.Derived.HausdorffCompletionUnitUp
