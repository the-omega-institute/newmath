import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoublingMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DoublingMetricSpaceUp : Type where
  | mk (X M B R K E T S H C P N : BHist) : DoublingMetricSpaceUp
  deriving DecidableEq

def doublingMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doublingMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doublingMetricSpaceEncodeBHist h

def doublingMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doublingMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doublingMetricSpaceDecodeBHist tail)

private theorem DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def doublingMetricSpaceFields : DoublingMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoublingMetricSpaceUp.mk X M B R K E T S H C P N => [X, M, B, R, K, E, T, S, H, C, P, N]

def doublingMetricSpaceToEventFlow : DoublingMetricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (doublingMetricSpaceFields x).map doublingMetricSpaceEncodeBHist

private def doublingMetricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => doublingMetricSpaceEventAtDefault index rest

def doublingMetricSpaceFromEventFlow (ef : EventFlow) : Option DoublingMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DoublingMetricSpaceUp.mk
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 0 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 1 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 2 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 3 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 4 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 5 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 6 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 7 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 8 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 9 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 10 ef))
      (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEventAtDefault 11 ef)))

private theorem DoublingMetricSpaceTasteGate_single_carrier_alignment_round_trip
    (x : DoublingMetricSpaceUp) :
    doublingMetricSpaceFromEventFlow (doublingMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X M B R K E T S H C P N =>
      change
        some
          (DoublingMetricSpaceUp.mk
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist X))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist M))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist B))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist R))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist K))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist E))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist T))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist S))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist H))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist C))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist P))
            (doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist N))) =
          some (DoublingMetricSpaceUp.mk X M B R K E T S H C P N)
      rw [DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode X,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode M,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode B,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode R,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode K,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode E,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode T,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode S,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode H,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode C,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode P,
        DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem DoublingMetricSpaceToEventFlow_injective {x y : DoublingMetricSpaceUp} :
    doublingMetricSpaceToEventFlow x = doublingMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doublingMetricSpaceFromEventFlow (doublingMetricSpaceToEventFlow x) =
        doublingMetricSpaceFromEventFlow (doublingMetricSpaceToEventFlow y) :=
    congrArg doublingMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DoublingMetricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DoublingMetricSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance doublingMetricSpaceBHistCarrier : BHistCarrier DoublingMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doublingMetricSpaceToEventFlow
  fromEventFlow := doublingMetricSpaceFromEventFlow

instance doublingMetricSpaceChapterTasteGate : ChapterTasteGate DoublingMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doublingMetricSpaceFromEventFlow (doublingMetricSpaceToEventFlow x) = some x
    exact DoublingMetricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DoublingMetricSpaceToEventFlow_injective heq)

theorem DoublingMetricSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, doublingMetricSpaceDecodeBHist (doublingMetricSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DoublingMetricSpaceUp) ∧
        Nonempty (ChapterTasteGate DoublingMetricSpaceUp) ∧
          doublingMetricSpaceFields
              (DoublingMetricSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact DoublingMetricSpaceTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨doublingMetricSpaceBHistCarrier⟩
    · constructor
      · exact ⟨doublingMetricSpaceChapterTasteGate⟩
      · rfl

end BEDC.Derived.DoublingMetricSpaceUp
