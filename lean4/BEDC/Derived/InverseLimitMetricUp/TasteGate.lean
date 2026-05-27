import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InverseLimitMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InverseLimitMetricUp : Type where
  | mk (D Pi W Q R L H C P N : BHist) : InverseLimitMetricUp

def inverseLimitMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inverseLimitMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inverseLimitMetricEncodeBHist h

def inverseLimitMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inverseLimitMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inverseLimitMetricDecodeBHist tail)

private theorem inverseLimitMetric_decode_encode_bhist :
    ∀ h : BHist, inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def inverseLimitMetricFields : InverseLimitMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InverseLimitMetricUp.mk D Pi W Q R L H C P N => [D, Pi, W, Q, R, L, H, C, P, N]

def inverseLimitMetricToEventFlow : InverseLimitMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map inverseLimitMetricEncodeBHist (inverseLimitMetricFields x)

def inverseLimitMetricFromEventFlow : EventFlow → Option InverseLimitMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: Pi :: W :: Q :: R :: L :: H :: C :: P :: N :: [] =>
      some
        (InverseLimitMetricUp.mk
          (inverseLimitMetricDecodeBHist D)
          (inverseLimitMetricDecodeBHist Pi)
          (inverseLimitMetricDecodeBHist W)
          (inverseLimitMetricDecodeBHist Q)
          (inverseLimitMetricDecodeBHist R)
          (inverseLimitMetricDecodeBHist L)
          (inverseLimitMetricDecodeBHist H)
          (inverseLimitMetricDecodeBHist C)
          (inverseLimitMetricDecodeBHist P)
          (inverseLimitMetricDecodeBHist N))
  | _ => none

private theorem InverseLimitMetricTasteGate_single_carrier_alignment_round_trip
    (x : InverseLimitMetricUp) :
    inverseLimitMetricFromEventFlow (inverseLimitMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D Pi W Q R L H C P N =>
      change
        some
          (InverseLimitMetricUp.mk
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist D))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist Pi))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist W))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist Q))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist R))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist L))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist H))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist C))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist P))
            (inverseLimitMetricDecodeBHist (inverseLimitMetricEncodeBHist N))) =
          some (InverseLimitMetricUp.mk D Pi W Q R L H C P N)
      rw [inverseLimitMetric_decode_encode_bhist D,
        inverseLimitMetric_decode_encode_bhist Pi,
        inverseLimitMetric_decode_encode_bhist W,
        inverseLimitMetric_decode_encode_bhist Q,
        inverseLimitMetric_decode_encode_bhist R,
        inverseLimitMetric_decode_encode_bhist L,
        inverseLimitMetric_decode_encode_bhist H,
        inverseLimitMetric_decode_encode_bhist C,
        inverseLimitMetric_decode_encode_bhist P,
        inverseLimitMetric_decode_encode_bhist N]

private theorem InverseLimitMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : InverseLimitMetricUp} :
    inverseLimitMetricToEventFlow x = inverseLimitMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inverseLimitMetricFromEventFlow (inverseLimitMetricToEventFlow x) =
        inverseLimitMetricFromEventFlow (inverseLimitMetricToEventFlow y) :=
    congrArg inverseLimitMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (InverseLimitMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (InverseLimitMetricTasteGate_single_carrier_alignment_round_trip y)))

instance inverseLimitMetricBHistCarrier : BHistCarrier InverseLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inverseLimitMetricToEventFlow
  fromEventFlow := inverseLimitMetricFromEventFlow

instance inverseLimitMetricChapterTasteGate :
    ChapterTasteGate InverseLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inverseLimitMetricFromEventFlow (inverseLimitMetricToEventFlow x) = some x
    exact InverseLimitMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (InverseLimitMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def inverseLimitMetricTasteGate : ChapterTasteGate InverseLimitMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inverseLimitMetricChapterTasteGate

end BEDC.Derived.InverseLimitMetricUp
