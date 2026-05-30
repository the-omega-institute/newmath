import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionUniversalPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionUniversalPropertyUp : Type where
  | mk (M C E U Q W D R H T P N : BHist) : MetricCompletionUniversalPropertyUp

def metricCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionUniversalPropertyEncodeBHist h

def metricCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionUniversalPropertyDecodeBHist tail)

private theorem MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionUniversalPropertyFields :
    MetricCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionUniversalPropertyUp.mk M C E U Q W D R H T P N =>
      [M, C, E, U, Q, W, D, R, H, T, P, N]

def metricCompletionUniversalPropertyToEventFlow :
    MetricCompletionUniversalPropertyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metricCompletionUniversalPropertyFields x).map
        metricCompletionUniversalPropertyEncodeBHist

private def metricCompletionUniversalPropertyRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => metricCompletionUniversalPropertyRawAt index rest

def metricCompletionUniversalPropertyFromEventFlow
    (flow : EventFlow) : Option MetricCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricCompletionUniversalPropertyUp.mk
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 0 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 1 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 2 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 3 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 4 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 5 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 6 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 7 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 8 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 9 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 10 flow))
      (metricCompletionUniversalPropertyDecodeBHist
        (metricCompletionUniversalPropertyRawAt 11 flow)))

private theorem MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip
    (x : MetricCompletionUniversalPropertyUp) :
    metricCompletionUniversalPropertyFromEventFlow
        (metricCompletionUniversalPropertyToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M C E U Q W D R H T P N =>
      change
        some
          (MetricCompletionUniversalPropertyUp.mk
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist M))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist C))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist E))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist U))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist Q))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist W))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist D))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist R))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist H))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist T))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist P))
            (metricCompletionUniversalPropertyDecodeBHist
              (metricCompletionUniversalPropertyEncodeBHist N))) =
          some (MetricCompletionUniversalPropertyUp.mk M C E U Q W D R H T P N)
      rw [MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode M,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode C,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode E,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode U,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode Q,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode W,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode D,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode R,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode H,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode T,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode P,
        MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode_encode N]

private theorem MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricCompletionUniversalPropertyUp} :
    metricCompletionUniversalPropertyToEventFlow x =
      metricCompletionUniversalPropertyToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionUniversalPropertyFromEventFlow
          (metricCompletionUniversalPropertyToEventFlow x) =
        metricCompletionUniversalPropertyFromEventFlow
          (metricCompletionUniversalPropertyToEventFlow y) :=
    congrArg metricCompletionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip y)))

instance metricCompletionUniversalPropertyBHistCarrier :
    BHistCarrier MetricCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionUniversalPropertyToEventFlow
  fromEventFlow := metricCompletionUniversalPropertyFromEventFlow

instance metricCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate MetricCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionUniversalPropertyFromEventFlow
          (metricCompletionUniversalPropertyToEventFlow x) =
        some x
    exact MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    ChapterTasteGate MetricCompletionUniversalPropertyUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact metricCompletionUniversalPropertyChapterTasteGate

end BEDC.Derived.MetricCompletionUniversalPropertyUp
