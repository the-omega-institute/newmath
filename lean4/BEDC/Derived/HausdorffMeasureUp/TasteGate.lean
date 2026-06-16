import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffMeasureUp : Type where
  | mk (M D R O B C S T E K P N : BHist) : HausdorffMeasureUp
  deriving DecidableEq

def hausdorffMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffMeasureEncodeBHist h

def hausdorffMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffMeasureDecodeBHist tail)

private theorem HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffMeasureFields : HausdorffMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffMeasureUp.mk M D R O B C S T E K P N => [M, D, R, O, B, C, S, T, E, K, P, N]

def hausdorffMeasureToEventFlow : HausdorffMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hausdorffMeasureFields x).map hausdorffMeasureEncodeBHist

private def hausdorffMeasureEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hausdorffMeasureEventAt index rest

def hausdorffMeasureFromEventFlow : EventFlow → Option HausdorffMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (HausdorffMeasureUp.mk
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 0 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 1 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 2 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 3 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 4 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 5 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 6 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 7 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 8 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 9 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 10 ef))
        (hausdorffMeasureDecodeBHist (hausdorffMeasureEventAt 11 ef)))

private theorem hausdorffMeasure_round_trip :
    ∀ x : HausdorffMeasureUp,
      hausdorffMeasureFromEventFlow (hausdorffMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D R O B C S T E K P N =>
      change
        some
          (HausdorffMeasureUp.mk
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist M))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist D))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist R))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist O))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist B))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist C))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist S))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist T))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist E))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist K))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist P))
            (hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist N))) =
          some (HausdorffMeasureUp.mk M D R O B C S T E K P N)
      rw [HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode M,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode D,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode R,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode O,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode B,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode C,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode S,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode T,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode E,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode K,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode P,
        HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode N]

private theorem hausdorffMeasureToEventFlow_injective {x y : HausdorffMeasureUp} :
    hausdorffMeasureToEventFlow x = hausdorffMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffMeasureFromEventFlow (hausdorffMeasureToEventFlow x) =
        hausdorffMeasureFromEventFlow (hausdorffMeasureToEventFlow y) :=
    congrArg hausdorffMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hausdorffMeasure_round_trip x).symm
      (Eq.trans hread (hausdorffMeasure_round_trip y)))

private theorem hausdorffMeasure_field_faithful :
    ∀ x y : HausdorffMeasureUp, hausdorffMeasureFields x = hausdorffMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 D1 R1 O1 B1 C1 S1 T1 E1 K1 P1 N1 =>
      cases y with
      | mk M2 D2 R2 O2 B2 C2 S2 T2 E2 K2 P2 N2 =>
          cases hfields
          rfl

instance hausdorffMeasureBHistCarrier : BHistCarrier HausdorffMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffMeasureToEventFlow
  fromEventFlow := hausdorffMeasureFromEventFlow

instance hausdorffMeasureChapterTasteGate : ChapterTasteGate HausdorffMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffMeasureFromEventFlow (hausdorffMeasureToEventFlow x) = some x
    exact hausdorffMeasure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hausdorffMeasureToEventFlow_injective heq)

instance hausdorffMeasureFieldFaithful : FieldFaithful HausdorffMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffMeasureFields
  field_faithful := hausdorffMeasure_field_faithful

instance hausdorffMeasureNontrivial : Nontrivial HausdorffMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffMeasureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem HausdorffMeasureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HausdorffMeasureUp) ∧
      Nonempty (FieldFaithful HausdorffMeasureUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HausdorffMeasureUp) ∧
          (∀ h : BHist, hausdorffMeasureDecodeBHist (hausdorffMeasureEncodeBHist h) = h) ∧
            (∀ x : HausdorffMeasureUp,
              hausdorffMeasureFromEventFlow (hausdorffMeasureToEventFlow x) = some x) ∧
              (∀ x y : HausdorffMeasureUp,
                hausdorffMeasureToEventFlow x = hausdorffMeasureToEventFlow y → x = y) ∧
                hausdorffMeasureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨hausdorffMeasureChapterTasteGate⟩
  constructor
  · exact ⟨hausdorffMeasureFieldFaithful⟩
  constructor
  · exact ⟨hausdorffMeasureNontrivial⟩
  constructor
  · exact HausdorffMeasureTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact hausdorffMeasure_round_trip
  constructor
  · intro x y heq
    exact hausdorffMeasureToEventFlow_injective heq
  · rfl

end BEDC.Derived.HausdorffMeasureUp
