import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DoublingMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DoublingMetricUp : Type where
  | mk (M rho B K E T S H C P N : BHist) : DoublingMetricUp
  deriving DecidableEq

def doublingMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: doublingMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: doublingMetricEncodeBHist h

def doublingMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (doublingMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (doublingMetricDecodeBHist tail)

private theorem doublingMetric_decode_encode_bhist :
    ∀ h : BHist, doublingMetricDecodeBHist (doublingMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def doublingMetricFields : DoublingMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DoublingMetricUp.mk M rho B K E T S H C P N => [M, rho, B, K, E, T, S, H, C, P, N]

def doublingMetricToEventFlow : DoublingMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (doublingMetricFields x).map doublingMetricEncodeBHist

private def doublingMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => doublingMetricEventAtDefault index rest

def doublingMetricFromEventFlow (ef : EventFlow) : Option DoublingMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DoublingMetricUp.mk
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 0 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 1 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 2 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 3 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 4 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 5 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 6 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 7 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 8 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 9 ef))
      (doublingMetricDecodeBHist (doublingMetricEventAtDefault 10 ef)))

private theorem doublingMetric_round_trip :
    ∀ x : DoublingMetricUp,
      doublingMetricFromEventFlow (doublingMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M rho B K E T S H C P N =>
      change
        some
          (DoublingMetricUp.mk
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist M))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist rho))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist B))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist K))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist E))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist T))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist S))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist H))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist C))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist P))
            (doublingMetricDecodeBHist (doublingMetricEncodeBHist N))) =
          some (DoublingMetricUp.mk M rho B K E T S H C P N)
      rw [doublingMetric_decode_encode_bhist M,
        doublingMetric_decode_encode_bhist rho,
        doublingMetric_decode_encode_bhist B,
        doublingMetric_decode_encode_bhist K,
        doublingMetric_decode_encode_bhist E,
        doublingMetric_decode_encode_bhist T,
        doublingMetric_decode_encode_bhist S,
        doublingMetric_decode_encode_bhist H,
        doublingMetric_decode_encode_bhist C,
        doublingMetric_decode_encode_bhist P,
        doublingMetric_decode_encode_bhist N]

private theorem doublingMetricToEventFlow_injective {x y : DoublingMetricUp} :
    doublingMetricToEventFlow x = doublingMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      doublingMetricFromEventFlow (doublingMetricToEventFlow x) =
        doublingMetricFromEventFlow (doublingMetricToEventFlow y) :=
    congrArg doublingMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (doublingMetric_round_trip x).symm
      (Eq.trans hread (doublingMetric_round_trip y)))

private theorem doublingMetric_fields_faithful :
    ∀ x y : DoublingMetricUp, doublingMetricFields x = doublingMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 rho1 B1 K1 E1 T1 S1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 rho2 B2 K2 E2 T2 S2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance doublingMetricBHistCarrier : BHistCarrier DoublingMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := doublingMetricToEventFlow
  fromEventFlow := doublingMetricFromEventFlow

instance doublingMetricChapterTasteGate : ChapterTasteGate DoublingMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change doublingMetricFromEventFlow (doublingMetricToEventFlow x) = some x
    exact doublingMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (doublingMetricToEventFlow_injective heq)

instance doublingMetricFieldFaithful : FieldFaithful DoublingMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := doublingMetricFields
  field_faithful := doublingMetric_fields_faithful

def taste_gate : ChapterTasteGate DoublingMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  doublingMetricChapterTasteGate

theorem DoublingMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, doublingMetricDecodeBHist (doublingMetricEncodeBHist h) = h) ∧
      (∀ x : DoublingMetricUp,
        doublingMetricFromEventFlow (doublingMetricToEventFlow x) = some x) ∧
        (∀ x y : DoublingMetricUp,
          doublingMetricToEventFlow x = doublingMetricToEventFlow y → x = y) ∧
          doublingMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨doublingMetric_decode_encode_bhist,
      doublingMetric_round_trip,
      (fun _ _ heq => doublingMetricToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DoublingMetricUp
