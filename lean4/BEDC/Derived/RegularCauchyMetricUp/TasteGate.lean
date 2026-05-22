import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMetricUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMetricUp : Type where
  | mk : (left right window tolerance distance realSeal transport replay provenance name : BHist) →
      RegularCauchyMetricUp
  deriving DecidableEq

def regularCauchyMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMetricEncodeBHist h

def regularCauchyMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMetricDecodeBHist tail)

private theorem regularCauchyMetric_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyMetricFields : RegularCauchyMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMetricUp.mk left right window tolerance distance realSeal transport replay
      provenance name =>
      [left, right, window, tolerance, distance, realSeal, transport, replay, provenance, name]

def regularCauchyMetricToEventFlow : RegularCauchyMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMetricUp.mk left right window tolerance distance realSeal transport replay
      provenance name =>
      [[BMark.b1, BMark.b0, BMark.b0],
        regularCauchyMetricEncodeBHist left,
        regularCauchyMetricEncodeBHist right,
        regularCauchyMetricEncodeBHist window,
        regularCauchyMetricEncodeBHist tolerance,
        regularCauchyMetricEncodeBHist distance,
        regularCauchyMetricEncodeBHist realSeal,
        regularCauchyMetricEncodeBHist transport,
        regularCauchyMetricEncodeBHist replay,
        regularCauchyMetricEncodeBHist provenance,
        regularCauchyMetricEncodeBHist name]

private def regularCauchyMetricEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMetricEventAt index rest

def regularCauchyMetricFromEventFlow : EventFlow → Option RegularCauchyMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RegularCauchyMetricUp.mk
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 1 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 2 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 3 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 4 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 5 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 6 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 7 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 8 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 9 ef))
          (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAt 10 ef)))

private theorem regularCauchyMetric_round_trip :
    ∀ x : RegularCauchyMetricUp,
      regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right window tolerance distance realSeal transport replay provenance name =>
      change
        some
          (RegularCauchyMetricUp.mk
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist left))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist right))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist window))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist tolerance))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist distance))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist realSeal))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist transport))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist replay))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist provenance))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist name))) =
          some
            (RegularCauchyMetricUp.mk left right window tolerance distance realSeal transport replay
              provenance name)
      rw [regularCauchyMetric_decode_encode_bhist left,
        regularCauchyMetric_decode_encode_bhist right,
        regularCauchyMetric_decode_encode_bhist window,
        regularCauchyMetric_decode_encode_bhist tolerance,
        regularCauchyMetric_decode_encode_bhist distance,
        regularCauchyMetric_decode_encode_bhist realSeal,
        regularCauchyMetric_decode_encode_bhist transport,
        regularCauchyMetric_decode_encode_bhist replay,
        regularCauchyMetric_decode_encode_bhist provenance,
        regularCauchyMetric_decode_encode_bhist name]

private theorem regularCauchyMetricToEventFlow_injective {x y : RegularCauchyMetricUp} :
    regularCauchyMetricToEventFlow x = regularCauchyMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) =
        regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow y) :=
    congrArg regularCauchyMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyMetric_round_trip x).symm
      (Eq.trans hread (regularCauchyMetric_round_trip y)))

private theorem regularCauchyMetric_field_faithful :
    ∀ x y : RegularCauchyMetricUp,
      regularCauchyMetricFields x = regularCauchyMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk left₁ right₁ window₁ tolerance₁ distance₁ realSeal₁ transport₁ replay₁ provenance₁
      name₁ =>
      cases y with
      | mk left₂ right₂ window₂ tolerance₂ distance₂ realSeal₂ transport₂ replay₂ provenance₂
          name₂ =>
          cases h
          rfl

instance regularCauchyMetricBHistCarrier : BHistCarrier RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMetricToEventFlow
  fromEventFlow := regularCauchyMetricFromEventFlow

instance regularCauchyMetricChapterTasteGate : ChapterTasteGate RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x
    exact regularCauchyMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMetricToEventFlow_injective heq)

instance regularCauchyMetricFieldFaithful : FieldFaithful RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyMetricFields
  field_faithful := regularCauchyMetric_field_faithful

instance regularCauchyMetricNontrivial : Nontrivial RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMetricChapterTasteGate

theorem RegularCauchyMetricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyMetricUp) ∧
      Nonempty (FieldFaithful RegularCauchyMetricUp) ∧
      Nonempty (Nontrivial RegularCauchyMetricUp) ∧
      (∀ h : BHist,
        regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMetricUp,
        regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyMetricUp,
        regularCauchyMetricToEventFlow x = regularCauchyMetricToEventFlow y → x = y) ∧
      regularCauchyMetricEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨regularCauchyMetricChapterTasteGate⟩
  · constructor
    · exact ⟨regularCauchyMetricFieldFaithful⟩
    · constructor
      · exact ⟨regularCauchyMetricNontrivial⟩
      · constructor
        · exact regularCauchyMetric_decode_encode_bhist
        · constructor
          · exact regularCauchyMetric_round_trip
          · constructor
            · intro x y heq
              exact regularCauchyMetricToEventFlow_injective heq
            · rfl

end BEDC.Derived.RegularCauchyMetricUp.TasteGate
