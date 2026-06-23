import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrownianBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrownianBridgeUp : Type where
  | mk (W T E K S Q R H C P N : BHist) : BrownianBridgeUp
  deriving DecidableEq

def brownianBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brownianBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brownianBridgeEncodeBHist h

def brownianBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brownianBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brownianBridgeDecodeBHist tail)

private theorem BrownianBridgeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, brownianBridgeDecodeBHist (brownianBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brownianBridgeFields : BrownianBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrownianBridgeUp.mk W T E K S Q R H C P N => [W, T, E, K, S, Q, R, H, C, P, N]

def brownianBridgeToEventFlow : BrownianBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (brownianBridgeFields x).map brownianBridgeEncodeBHist

private def brownianBridgeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brownianBridgeEventAt index rest

def brownianBridgeFromEventFlow (ef : EventFlow) : Option BrownianBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrownianBridgeUp.mk
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 0 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 1 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 2 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 3 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 4 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 5 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 6 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 7 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 8 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 9 ef))
      (brownianBridgeDecodeBHist (brownianBridgeEventAt 10 ef)))

private theorem BrownianBridgeTasteGate_single_carrier_alignment_round_trip
    (x : BrownianBridgeUp) :
    brownianBridgeFromEventFlow (brownianBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W T E K S Q R H C P N =>
      change
        some
          (BrownianBridgeUp.mk
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist W))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist T))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist E))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist K))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist S))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist Q))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist R))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist H))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist C))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist P))
            (brownianBridgeDecodeBHist (brownianBridgeEncodeBHist N))) =
          some (BrownianBridgeUp.mk W T E K S Q R H C P N)
      rw [BrownianBridgeTasteGate_single_carrier_alignment_decode_encode W,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode T,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode E,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode K,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode S,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode Q,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode R,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode H,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode C,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode P,
        BrownianBridgeTasteGate_single_carrier_alignment_decode_encode N]

private theorem BrownianBridgeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BrownianBridgeUp} :
    brownianBridgeToEventFlow x = brownianBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brownianBridgeFromEventFlow (brownianBridgeToEventFlow x) =
        brownianBridgeFromEventFlow (brownianBridgeToEventFlow y) :=
    congrArg brownianBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BrownianBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BrownianBridgeTasteGate_single_carrier_alignment_round_trip y)))

instance brownianBridgeBHistCarrier : BHistCarrier BrownianBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brownianBridgeToEventFlow
  fromEventFlow := brownianBridgeFromEventFlow

instance brownianBridgeChapterTasteGate : ChapterTasteGate BrownianBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brownianBridgeFromEventFlow (brownianBridgeToEventFlow x) = some x
    exact BrownianBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BrownianBridgeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def BrownianBridgeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BrownianBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brownianBridgeChapterTasteGate

theorem BrownianBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, brownianBridgeDecodeBHist (brownianBridgeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BrownianBridgeUp) ∧
        Nonempty (ChapterTasteGate BrownianBridgeUp) ∧
          brownianBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BrownianBridgeTasteGate_single_carrier_alignment_decode_encode,
      ⟨brownianBridgeBHistCarrier⟩,
      ⟨brownianBridgeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BrownianBridgeUp
