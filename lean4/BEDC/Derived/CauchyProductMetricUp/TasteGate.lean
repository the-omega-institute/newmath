import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductMetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductMetricUp : Type where
  | mk
      (left right leftWindow rightWindow leftReadback rightReadback dyadicLedger
        distance realSeal transport replay provenance name : BHist) :
      CauchyProductMetricUp
  deriving DecidableEq

def cauchyProductMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductMetricEncodeBHist h

def cauchyProductMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductMetricDecodeBHist tail)

private theorem cauchyProductMetric_decode_encode_bhist :
    ∀ h : BHist, cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductMetricFields : CauchyProductMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductMetricUp.mk L R WL WR QL QR D Delta E H C P N =>
      [L, R, WL, WR, QL, QR, D, Delta, E, H, C, P, N]

def cauchyProductMetricToEventFlow : CauchyProductMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyProductMetricFields x).map cauchyProductMetricEncodeBHist

private def cauchyProductMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyProductMetricEventAtDefault index rest

def cauchyProductMetricFromEventFlow (ef : EventFlow) : Option CauchyProductMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductMetricUp.mk
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 0 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 1 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 2 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 3 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 4 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 5 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 6 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 7 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 8 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 9 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 10 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 11 ef))
      (cauchyProductMetricDecodeBHist (cauchyProductMetricEventAtDefault 12 ef)))

private theorem cauchyProductMetric_round_trip (x : CauchyProductMetricUp) :
    cauchyProductMetricFromEventFlow (cauchyProductMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L R WL WR QL QR D Delta E H C P N =>
      change
        some
          (CauchyProductMetricUp.mk
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist L))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist R))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist WL))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist WR))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist QL))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist QR))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist D))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist Delta))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist E))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist H))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist C))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist P))
            (cauchyProductMetricDecodeBHist (cauchyProductMetricEncodeBHist N))) =
          some (CauchyProductMetricUp.mk L R WL WR QL QR D Delta E H C P N)
      rw [cauchyProductMetric_decode_encode_bhist L,
        cauchyProductMetric_decode_encode_bhist R,
        cauchyProductMetric_decode_encode_bhist WL,
        cauchyProductMetric_decode_encode_bhist WR,
        cauchyProductMetric_decode_encode_bhist QL,
        cauchyProductMetric_decode_encode_bhist QR,
        cauchyProductMetric_decode_encode_bhist D,
        cauchyProductMetric_decode_encode_bhist Delta,
        cauchyProductMetric_decode_encode_bhist E,
        cauchyProductMetric_decode_encode_bhist H,
        cauchyProductMetric_decode_encode_bhist C,
        cauchyProductMetric_decode_encode_bhist P,
        cauchyProductMetric_decode_encode_bhist N]

private theorem cauchyProductMetricToEventFlow_injective {x y : CauchyProductMetricUp} :
    cauchyProductMetricToEventFlow x = cauchyProductMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductMetricFromEventFlow (cauchyProductMetricToEventFlow x) =
        cauchyProductMetricFromEventFlow (cauchyProductMetricToEventFlow y) :=
    congrArg cauchyProductMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyProductMetric_round_trip x).symm
      (Eq.trans hread (cauchyProductMetric_round_trip y)))

instance cauchyProductMetricBHistCarrier : BHistCarrier CauchyProductMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductMetricToEventFlow
  fromEventFlow := cauchyProductMetricFromEventFlow

instance cauchyProductMetricChapterTasteGate : ChapterTasteGate CauchyProductMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyProductMetricFromEventFlow (cauchyProductMetricToEventFlow x) = some x
    exact cauchyProductMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyProductMetricToEventFlow_injective heq)

def cauchyProductMetricTasteGate : ChapterTasteGate CauchyProductMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductMetricChapterTasteGate

theorem CauchyProductMetricTasteGate_single_carrier_alignment :
    (∀ x : CauchyProductMetricUp,
      ∃ L R WL WR QL QR D Delta E H C P N replay : BHist,
        x = CauchyProductMetricUp.mk L R WL WR QL QR D Delta E H C P N ∧
          cauchyProductMetricFields x = [L, R, WL, WR, QL, QR, D, Delta, E, H, C, P, N] ∧
            Cont Delta E replay) ∧
      Nonempty (BHistCarrier CauchyProductMetricUp) ∧
        Nonempty (ChapterTasteGate CauchyProductMetricUp) := by
  -- BEDC touchpoint anchor: BHist BMark Cont ChapterTasteGate
  constructor
  · intro x
    cases x with
    | mk L R WL WR QL QR D Delta E H C P N =>
        exact
          ⟨L, R, WL, WR, QL, QR, D, Delta, E, H, C, P, N, append Delta E,
            rfl, rfl, rfl⟩
  · exact ⟨⟨cauchyProductMetricBHistCarrier⟩, ⟨cauchyProductMetricChapterTasteGate⟩⟩

end BEDC.Derived.CauchyProductMetricUp
