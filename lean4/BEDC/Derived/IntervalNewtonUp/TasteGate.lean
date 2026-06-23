import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalNewtonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalNewtonUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (B F D N K V R H C P L : BHist) : IntervalNewtonUp
  deriving DecidableEq

def intervalNewtonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalNewtonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalNewtonEncodeBHist h

def intervalNewtonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalNewtonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalNewtonDecodeBHist tail)

private theorem IntervalNewtonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, intervalNewtonDecodeBHist (intervalNewtonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalNewtonFields : IntervalNewtonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalNewtonUp.mk B F D N K V R H C P L => [B, F, D, N, K, V, R, H, C, P, L]

def intervalNewtonToEventFlow : IntervalNewtonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (intervalNewtonFields x).map intervalNewtonEncodeBHist

private def intervalNewtonEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => intervalNewtonEventAt index rest

def intervalNewtonFromEventFlow (ef : EventFlow) : Option IntervalNewtonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalNewtonUp.mk
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 0 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 1 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 2 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 3 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 4 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 5 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 6 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 7 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 8 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 9 ef))
      (intervalNewtonDecodeBHist (intervalNewtonEventAt 10 ef)))

private theorem IntervalNewtonTasteGate_single_carrier_alignment_round_trip
    (x : IntervalNewtonUp) :
    intervalNewtonFromEventFlow (intervalNewtonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B F D N K V R H C P L =>
      change
        some
          (IntervalNewtonUp.mk
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist B))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist F))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist D))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist N))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist K))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist V))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist R))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist H))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist C))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist P))
            (intervalNewtonDecodeBHist (intervalNewtonEncodeBHist L))) =
          some (IntervalNewtonUp.mk B F D N K V R H C P L)
      rw [IntervalNewtonTasteGate_single_carrier_alignment_decode_encode B,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode F,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode D,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode N,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode K,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode V,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode R,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode H,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode C,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode P,
        IntervalNewtonTasteGate_single_carrier_alignment_decode_encode L]

private theorem IntervalNewtonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntervalNewtonUp} :
    intervalNewtonToEventFlow x = intervalNewtonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalNewtonFromEventFlow (intervalNewtonToEventFlow x) =
        intervalNewtonFromEventFlow (intervalNewtonToEventFlow y) :=
    congrArg intervalNewtonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IntervalNewtonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntervalNewtonTasteGate_single_carrier_alignment_round_trip y)))

instance intervalNewtonBHistCarrier : BHistCarrier IntervalNewtonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalNewtonToEventFlow
  fromEventFlow := intervalNewtonFromEventFlow

instance intervalNewtonChapterTasteGate : ChapterTasteGate IntervalNewtonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change intervalNewtonFromEventFlow (intervalNewtonToEventFlow x) = some x
    exact IntervalNewtonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalNewtonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate IntervalNewtonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  intervalNewtonChapterTasteGate

theorem IntervalNewtonTasteGate_single_carrier_alignment :
    (∀ h : BHist, intervalNewtonDecodeBHist (intervalNewtonEncodeBHist h) = h) ∧
      (∀ x : IntervalNewtonUp, intervalNewtonFromEventFlow (intervalNewtonToEventFlow x) =
        some x) ∧
        (∀ x y : IntervalNewtonUp,
          intervalNewtonToEventFlow x = intervalNewtonToEventFlow y → x = y) ∧
          intervalNewtonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨IntervalNewtonTasteGate_single_carrier_alignment_decode_encode,
      IntervalNewtonTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact IntervalNewtonTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.IntervalNewtonUp
