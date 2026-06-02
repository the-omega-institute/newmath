import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteMetricSpaceUp : Type where
  | mk (X D T B H C P N : BHist) : FiniteMetricSpaceUp

def finiteMetricSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteMetricSpaceEncodeBHist h

def finiteMetricSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteMetricSpaceDecodeBHist tail)

private theorem FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteMetricSpaceFields : FiniteMetricSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMetricSpaceUp.mk X D T B H C P N => [X, D, T, B, H, C, P, N]

def finiteMetricSpaceToEventFlow : FiniteMetricSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteMetricSpaceFields x).map finiteMetricSpaceEncodeBHist

private def finiteMetricSpaceEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteMetricSpaceEventAt index rest

def finiteMetricSpaceFromEventFlow (ef : EventFlow) : Option FiniteMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteMetricSpaceUp.mk
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 0 ef))
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 1 ef))
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 2 ef))
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 3 ef))
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 4 ef))
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 5 ef))
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 6 ef))
      (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEventAt 7 ef)))

private theorem FiniteMetricSpaceTasteGate_single_carrier_alignment_round_trip
    (x : FiniteMetricSpaceUp) :
    finiteMetricSpaceFromEventFlow (finiteMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X D T B H C P N =>
      change
        some
          (FiniteMetricSpaceUp.mk
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist X))
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist D))
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist T))
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist B))
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist H))
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist C))
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist P))
            (finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist N))) =
          some (FiniteMetricSpaceUp.mk X D T B H C P N)
      rw [FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode X,
        FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode D,
        FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode T,
        FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode B,
        FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode H,
        FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode C,
        FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode P,
        FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteMetricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteMetricSpaceUp} :
    finiteMetricSpaceToEventFlow x = finiteMetricSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteMetricSpaceFromEventFlow (finiteMetricSpaceToEventFlow x) =
        finiteMetricSpaceFromEventFlow (finiteMetricSpaceToEventFlow y) :=
    congrArg finiteMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteMetricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteMetricSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance finiteMetricSpaceBHistCarrier : BHistCarrier FiniteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteMetricSpaceToEventFlow
  fromEventFlow := finiteMetricSpaceFromEventFlow

instance finiteMetricSpaceChapterTasteGate : ChapterTasteGate FiniteMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteMetricSpaceFromEventFlow (finiteMetricSpaceToEventFlow x) = some x
    exact FiniteMetricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteMetricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteMetricSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, finiteMetricSpaceDecodeBHist (finiteMetricSpaceEncodeBHist h) = h) /\
      Nonempty (BHistCarrier FiniteMetricSpaceUp) /\
        Nonempty (ChapterTasteGate FiniteMetricSpaceUp) /\
          finiteMetricSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteMetricSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨finiteMetricSpaceBHistCarrier⟩,
      ⟨finiteMetricSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteMetricSpaceUp
