import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompleteMetricUp : Type where
  | mk (M F R S C E H K P N : BHist) : BishopCompleteMetricUp
  deriving DecidableEq

def bishopCompleteMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompleteMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompleteMetricEncodeBHist h

def bishopCompleteMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompleteMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompleteMetricDecodeBHist tail)

private theorem bishopCompleteMetric_decode_encode_bhist :
    ∀ h : BHist,
      bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompleteMetricFields : BishopCompleteMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompleteMetricUp.mk M F R S C E H K P N => [M, F, R, S, C, E, H, K, P, N]

def bishopCompleteMetricToEventFlow : BishopCompleteMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCompleteMetricFields x).map bishopCompleteMetricEncodeBHist

private def bishopCompleteMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompleteMetricEventAtDefault index rest

def bishopCompleteMetricFromEventFlow (ef : EventFlow) : Option BishopCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCompleteMetricUp.mk
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 0 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 1 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 2 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 3 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 4 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 5 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 6 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 7 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 8 ef))
      (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEventAtDefault 9 ef)))

private theorem bishopCompleteMetric_round_trip :
    ∀ x : BishopCompleteMetricUp,
      bishopCompleteMetricFromEventFlow (bishopCompleteMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F R S C E H K P N =>
      change
        some
          (BishopCompleteMetricUp.mk
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist M))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist F))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist R))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist S))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist C))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist E))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist H))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist K))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist P))
            (bishopCompleteMetricDecodeBHist (bishopCompleteMetricEncodeBHist N))) =
          some (BishopCompleteMetricUp.mk M F R S C E H K P N)
      rw [bishopCompleteMetric_decode_encode_bhist M,
        bishopCompleteMetric_decode_encode_bhist F,
        bishopCompleteMetric_decode_encode_bhist R,
        bishopCompleteMetric_decode_encode_bhist S,
        bishopCompleteMetric_decode_encode_bhist C,
        bishopCompleteMetric_decode_encode_bhist E,
        bishopCompleteMetric_decode_encode_bhist H,
        bishopCompleteMetric_decode_encode_bhist K,
        bishopCompleteMetric_decode_encode_bhist P,
        bishopCompleteMetric_decode_encode_bhist N]

private theorem bishopCompleteMetricToEventFlow_injective {x y : BishopCompleteMetricUp} :
    bishopCompleteMetricToEventFlow x = bishopCompleteMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompleteMetricFromEventFlow (bishopCompleteMetricToEventFlow x) =
        bishopCompleteMetricFromEventFlow (bishopCompleteMetricToEventFlow y) :=
    congrArg bishopCompleteMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopCompleteMetric_round_trip x).symm
      (Eq.trans hread (bishopCompleteMetric_round_trip y)))

instance bishopCompleteMetricBHistCarrier : BHistCarrier BishopCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompleteMetricToEventFlow
  fromEventFlow := bishopCompleteMetricFromEventFlow

instance bishopCompleteMetricChapterTasteGate : ChapterTasteGate BishopCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopCompleteMetricFromEventFlow (bishopCompleteMetricToEventFlow x) = some x
    exact bishopCompleteMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopCompleteMetricToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCompleteMetricChapterTasteGate

theorem BishopCompleteMetricTasteGate_single_carrier_alignment :
    (∀ x : BishopCompleteMetricUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (∀ x y : BishopCompleteMetricUp,
        x ≠ y → BHistCarrier.toEventFlow x ≠ BHistCarrier.toEventFlow y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro x
    change bishopCompleteMetricFromEventFlow (bishopCompleteMetricToEventFlow x) = some x
    exact bishopCompleteMetric_round_trip x
  · intro x y hxy heq
    change bishopCompleteMetricToEventFlow x = bishopCompleteMetricToEventFlow y at heq
    exact hxy (bishopCompleteMetricToEventFlow_injective heq)

end BEDC.Derived.BishopCompleteMetricUp
