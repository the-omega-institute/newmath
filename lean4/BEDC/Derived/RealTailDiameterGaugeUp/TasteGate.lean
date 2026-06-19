import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealTailDiameterGaugeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealTailDiameterGaugeUp : Type where
  | mk (E T D W R H C P N : BHist) : RealTailDiameterGaugeUp
  deriving DecidableEq

def realTailDiameterGaugeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realTailDiameterGaugeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realTailDiameterGaugeEncodeBHist h

def realTailDiameterGaugeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realTailDiameterGaugeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realTailDiameterGaugeDecodeBHist tail)

private theorem realTailDiameterGauge_decode_encode_bhist :
    ∀ h : BHist,
      realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realTailDiameterGaugeToEventFlow : RealTailDiameterGaugeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealTailDiameterGaugeUp.mk E T D W R H C P N =>
      [realTailDiameterGaugeEncodeBHist E,
        realTailDiameterGaugeEncodeBHist T,
        realTailDiameterGaugeEncodeBHist D,
        realTailDiameterGaugeEncodeBHist W,
        realTailDiameterGaugeEncodeBHist R,
        realTailDiameterGaugeEncodeBHist H,
        realTailDiameterGaugeEncodeBHist C,
        realTailDiameterGaugeEncodeBHist P,
        realTailDiameterGaugeEncodeBHist N]

private def realTailDiameterGaugeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realTailDiameterGaugeEventAt index rest

def realTailDiameterGaugeFromEventFlow :
    EventFlow → Option RealTailDiameterGaugeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealTailDiameterGaugeUp.mk
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 0 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 1 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 2 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 3 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 4 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 5 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 6 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 7 ef))
        (realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEventAt 8 ef)))

private theorem realTailDiameterGauge_round_trip :
    ∀ x : RealTailDiameterGaugeUp,
      realTailDiameterGaugeFromEventFlow
          (realTailDiameterGaugeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E T D W R H C P N =>
      change
        some
            (RealTailDiameterGaugeUp.mk
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist E))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist T))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist D))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist W))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist R))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist H))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist C))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist P))
              (realTailDiameterGaugeDecodeBHist
                (realTailDiameterGaugeEncodeBHist N))) =
          some (RealTailDiameterGaugeUp.mk E T D W R H C P N)
      rw [realTailDiameterGauge_decode_encode_bhist E,
        realTailDiameterGauge_decode_encode_bhist T,
        realTailDiameterGauge_decode_encode_bhist D,
        realTailDiameterGauge_decode_encode_bhist W,
        realTailDiameterGauge_decode_encode_bhist R,
        realTailDiameterGauge_decode_encode_bhist H,
        realTailDiameterGauge_decode_encode_bhist C,
        realTailDiameterGauge_decode_encode_bhist P,
        realTailDiameterGauge_decode_encode_bhist N]

private theorem realTailDiameterGaugeToEventFlow_injective
    {x y : RealTailDiameterGaugeUp} :
    realTailDiameterGaugeToEventFlow x =
      realTailDiameterGaugeToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realTailDiameterGaugeFromEventFlow
          (realTailDiameterGaugeToEventFlow x) =
        realTailDiameterGaugeFromEventFlow
          (realTailDiameterGaugeToEventFlow y) :=
    congrArg realTailDiameterGaugeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realTailDiameterGauge_round_trip x).symm
      (Eq.trans hread (realTailDiameterGauge_round_trip y)))

instance realTailDiameterGaugeBHistCarrier :
    BHistCarrier RealTailDiameterGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realTailDiameterGaugeToEventFlow
  fromEventFlow := realTailDiameterGaugeFromEventFlow

instance realTailDiameterGaugeChapterTasteGate :
    ChapterTasteGate RealTailDiameterGaugeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realTailDiameterGaugeFromEventFlow
          (realTailDiameterGaugeToEventFlow x) =
        some x
    exact realTailDiameterGauge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realTailDiameterGaugeToEventFlow_injective heq)

theorem RealTailDiameterGaugeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realTailDiameterGaugeDecodeBHist (realTailDiameterGaugeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealTailDiameterGaugeUp) ∧
        Nonempty (ChapterTasteGate RealTailDiameterGaugeUp) ∧
          realTailDiameterGaugeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realTailDiameterGauge_decode_encode_bhist,
      ⟨realTailDiameterGaugeBHistCarrier⟩,
      ⟨realTailDiameterGaugeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealTailDiameterGaugeUp.TasteGate
