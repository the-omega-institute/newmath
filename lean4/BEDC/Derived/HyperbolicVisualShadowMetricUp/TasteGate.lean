import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicVisualShadowMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicVisualShadowMetricUp : Type where
  | mk (U B M S G T H C P N : BHist) : HyperbolicVisualShadowMetricUp
  deriving DecidableEq

def hyperbolicVisualShadowMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicVisualShadowMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicVisualShadowMetricEncodeBHist h

def hyperbolicVisualShadowMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicVisualShadowMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicVisualShadowMetricDecodeBHist tail)

private theorem HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hyperbolicVisualShadowMetricDecodeBHist
          (hyperbolicVisualShadowMetricEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicVisualShadowMetricFields :
    HyperbolicVisualShadowMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicVisualShadowMetricUp.mk U B M S G T H C P N =>
      [U, B, M, S, G, T, H, C, P, N]

def hyperbolicVisualShadowMetricToEventFlow :
    HyperbolicVisualShadowMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicVisualShadowMetricFields x).map hyperbolicVisualShadowMetricEncodeBHist

private def hyperbolicVisualShadowMetricEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicVisualShadowMetricEventAt index rest

def hyperbolicVisualShadowMetricFromEventFlow (ef : EventFlow) :
    Option HyperbolicVisualShadowMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicVisualShadowMetricUp.mk
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 0 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 1 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 2 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 3 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 4 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 5 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 6 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 7 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 8 ef))
      (hyperbolicVisualShadowMetricDecodeBHist (hyperbolicVisualShadowMetricEventAt 9 ef)))

private theorem HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicVisualShadowMetricUp) :
    hyperbolicVisualShadowMetricFromEventFlow
        (hyperbolicVisualShadowMetricToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U B M S G T H C P N =>
      change
        some
          (HyperbolicVisualShadowMetricUp.mk
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist U))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist B))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist M))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist S))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist G))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist T))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist H))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist C))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist P))
            (hyperbolicVisualShadowMetricDecodeBHist
              (hyperbolicVisualShadowMetricEncodeBHist N))) =
          some (HyperbolicVisualShadowMetricUp.mk U B M S G T H C P N)
      rw [HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode U,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode B,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode M,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode S,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode G,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode T,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode H,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode C,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode P,
        HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode N]

private theorem HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicVisualShadowMetricUp} :
    hyperbolicVisualShadowMetricToEventFlow x =
        hyperbolicVisualShadowMetricToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicVisualShadowMetricFromEventFlow
          (hyperbolicVisualShadowMetricToEventFlow x) =
        hyperbolicVisualShadowMetricFromEventFlow
          (hyperbolicVisualShadowMetricToEventFlow y) :=
    congrArg hyperbolicVisualShadowMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : HyperbolicVisualShadowMetricUp,
      hyperbolicVisualShadowMetricFields x = hyperbolicVisualShadowMetricFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ B₁ M₁ S₁ G₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ B₂ M₂ S₂ G₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance hyperbolicVisualShadowMetricBHistCarrier :
    BHistCarrier HyperbolicVisualShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicVisualShadowMetricToEventFlow
  fromEventFlow := hyperbolicVisualShadowMetricFromEventFlow

instance hyperbolicVisualShadowMetricChapterTasteGate :
    ChapterTasteGate HyperbolicVisualShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicVisualShadowMetricFromEventFlow
          (hyperbolicVisualShadowMetricToEventFlow x) =
        some x
    exact HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance hyperbolicVisualShadowMetricFieldFaithful :
    FieldFaithful HyperbolicVisualShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicVisualShadowMetricFields
  field_faithful := HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_fields

instance hyperbolicVisualShadowMetricNontrivial :
    Nontrivial HyperbolicVisualShadowMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicVisualShadowMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicVisualShadowMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HyperbolicVisualShadowMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicVisualShadowMetricChapterTasteGate

theorem HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicVisualShadowMetricDecodeBHist
          (hyperbolicVisualShadowMetricEncodeBHist h) =
        h) ∧
      (∀ x : HyperbolicVisualShadowMetricUp,
        hyperbolicVisualShadowMetricFromEventFlow
            (hyperbolicVisualShadowMetricToEventFlow x) =
          some x) ∧
        (∀ x y : HyperbolicVisualShadowMetricUp,
          hyperbolicVisualShadowMetricToEventFlow x =
              hyperbolicVisualShadowMetricToEventFlow y →
            x = y) ∧
          hyperbolicVisualShadowMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_decode
  · constructor
    · exact HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact
          HyperbolicVisualShadowMetricTasteGate_single_carrier_alignment_toEventFlow_injective
            heq
      · rfl

end BEDC.Derived.HyperbolicVisualShadowMetricUp
