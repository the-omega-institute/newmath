import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricSpaceUp : Type where
  | mk (X sigma D Z S T H C P N : BHist) : MetricSpaceUp

def metricSpaceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricSpaceEncodeBHist h

def metricSpaceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricSpaceDecodeBHist tail)

private theorem MetricSpaceTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, metricSpaceDecodeBHist (metricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem MetricSpaceTasteGate_single_carrier_alignment_mk_congr
    {X X' sigma sigma' D D' Z Z' S S' T T' H H' C C' P P' N N' : BHist}
    (hX : X' = X) (hsigma : sigma' = sigma) (hD : D' = D) (hZ : Z' = Z)
    (hS : S' = S) (hT : T' = T) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    MetricSpaceUp.mk X' sigma' D' Z' S' T' H' C' P' N' =
      MetricSpaceUp.mk X sigma D Z S T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hsigma
  cases hD
  cases hZ
  cases hS
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def metricSpaceFields : MetricSpaceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricSpaceUp.mk X sigma D Z S T H C P N => [X, sigma, D, Z, S, T, H, C, P, N]

def metricSpaceToEventFlow : MetricSpaceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricSpaceFields x).map metricSpaceEncodeBHist

private def metricSpaceEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricSpaceEventAt index rest

def metricSpaceFromEventFlow (ef : EventFlow) : Option MetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricSpaceUp.mk
      (metricSpaceDecodeBHist (metricSpaceEventAt 0 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 1 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 2 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 3 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 4 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 5 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 6 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 7 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 8 ef))
      (metricSpaceDecodeBHist (metricSpaceEventAt 9 ef)))

private theorem MetricSpaceTasteGate_single_carrier_alignment_round_trip
    (x : MetricSpaceUp) :
    metricSpaceFromEventFlow (metricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X sigma D Z S T H C P N =>
      exact
        congrArg some
          (MetricSpaceTasteGate_single_carrier_alignment_mk_congr
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode X)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode sigma)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode D)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode Z)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode S)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode T)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode H)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode C)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode P)
            (MetricSpaceTasteGate_single_carrier_alignment_decode_encode N))

private theorem MetricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricSpaceUp} :
    metricSpaceToEventFlow x = metricSpaceToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricSpaceFromEventFlow (metricSpaceToEventFlow x) =
        metricSpaceFromEventFlow (metricSpaceToEventFlow y) :=
    congrArg metricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance metricSpaceBHistCarrier : BHistCarrier MetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricSpaceToEventFlow
  fromEventFlow := metricSpaceFromEventFlow

instance metricSpaceChapterTasteGate : ChapterTasteGate MetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricSpaceFromEventFlow (metricSpaceToEventFlow x) = some x
    exact MetricSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricSpaceTasteGate_single_carrier_alignment :
    (forall h : BHist, metricSpaceDecodeBHist (metricSpaceEncodeBHist h) = h) /\
      Nonempty (BHistCarrier MetricSpaceUp) /\
        Nonempty (ChapterTasteGate MetricSpaceUp) /\
          metricSpaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetricSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨metricSpaceBHistCarrier⟩,
      ⟨metricSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetricSpaceUp
