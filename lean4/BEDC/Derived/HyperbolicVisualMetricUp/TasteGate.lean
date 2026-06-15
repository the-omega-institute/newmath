import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicVisualMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicVisualMetricUp : Type where
  | mk (D M B S T F A H C P N : BHist) : HyperbolicVisualMetricUp
  deriving DecidableEq

def hyperbolicVisualMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicVisualMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicVisualMetricEncodeBHist h

def hyperbolicVisualMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicVisualMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicVisualMetricDecodeBHist tail)

private theorem HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicVisualMetricFields : HyperbolicVisualMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicVisualMetricUp.mk D M B S T F A H C P N => [D, M, B, S, T, F, A, H, C, P, N]

def hyperbolicVisualMetricToEventFlow : HyperbolicVisualMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicVisualMetricFields x).map hyperbolicVisualMetricEncodeBHist

private def hyperbolicVisualMetricEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicVisualMetricEventAt index rest

def hyperbolicVisualMetricFromEventFlow (ef : EventFlow) :
    Option HyperbolicVisualMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicVisualMetricUp.mk
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 0 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 1 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 2 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 3 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 4 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 5 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 6 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 7 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 8 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 9 ef))
      (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEventAt 10 ef)))

private theorem HyperbolicVisualMetricTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicVisualMetricUp) :
    hyperbolicVisualMetricFromEventFlow (hyperbolicVisualMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D M B S T F A H C P N =>
      change
        some
          (HyperbolicVisualMetricUp.mk
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist D))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist M))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist B))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist S))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist T))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist F))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist A))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist H))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist C))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist P))
            (hyperbolicVisualMetricDecodeBHist (hyperbolicVisualMetricEncodeBHist N))) =
          some (HyperbolicVisualMetricUp.mk D M B S T F A H C P N)
      rw [HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode D,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode M,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode B,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode S,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode T,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode F,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode A,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode H,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode C,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode P,
        HyperbolicVisualMetricTasteGate_single_carrier_alignment_decode N]

private theorem HyperbolicVisualMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyperbolicVisualMetricUp} :
    hyperbolicVisualMetricToEventFlow x = hyperbolicVisualMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicVisualMetricFromEventFlow (hyperbolicVisualMetricToEventFlow x) =
        hyperbolicVisualMetricFromEventFlow (hyperbolicVisualMetricToEventFlow y) :=
    congrArg hyperbolicVisualMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicVisualMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicVisualMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicVisualMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : HyperbolicVisualMetricUp,
      hyperbolicVisualMetricFields x = hyperbolicVisualMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ M₁ B₁ S₁ T₁ F₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ M₂ B₂ S₂ T₂ F₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance hyperbolicVisualMetricBHistCarrier : BHistCarrier HyperbolicVisualMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicVisualMetricToEventFlow
  fromEventFlow := hyperbolicVisualMetricFromEventFlow

instance hyperbolicVisualMetricChapterTasteGate :
    ChapterTasteGate HyperbolicVisualMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperbolicVisualMetricFromEventFlow (hyperbolicVisualMetricToEventFlow x) = some x
    exact HyperbolicVisualMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicVisualMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hyperbolicVisualMetricFieldFaithful :
    FieldFaithful HyperbolicVisualMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicVisualMetricFields
  field_faithful := HyperbolicVisualMetricTasteGate_single_carrier_alignment_fields

instance hyperbolicVisualMetricNontrivial : Nontrivial HyperbolicVisualMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicVisualMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperbolicVisualMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def HyperbolicVisualMetricTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HyperbolicVisualMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperbolicVisualMetricChapterTasteGate

theorem HyperbolicVisualMetricTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier HyperbolicVisualMetricUp) ∧
      Nonempty (ChapterTasteGate HyperbolicVisualMetricUp) ∧
        (∀ x : HyperbolicVisualMetricUp,
          hyperbolicVisualMetricFromEventFlow (hyperbolicVisualMetricToEventFlow x) = some x) ∧
          hyperbolicVisualMetricEncodeBHist BHist.Empty = ([] : RawEvent) ∧
            hyperbolicVisualMetricEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨hyperbolicVisualMetricBHistCarrier⟩,
      ⟨hyperbolicVisualMetricChapterTasteGate⟩,
      HyperbolicVisualMetricTasteGate_single_carrier_alignment_round_trip,
      rfl,
      rfl⟩

end BEDC.Derived.HyperbolicVisualMetricUp
