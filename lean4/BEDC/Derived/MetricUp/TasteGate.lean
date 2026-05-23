import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricUp : Type where
  | mk (x y d w c pi rho nu : BHist) : MetricUp
  deriving DecidableEq

def MetricTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: MetricTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: MetricTasteGate_single_carrier_alignment_encodeBHist h

def MetricTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (MetricTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (MetricTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem MetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      MetricTasteGate_single_carrier_alignment_decodeBHist
          (MetricTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def MetricTasteGate_single_carrier_alignment_fields : MetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricUp.mk x y d w c pi rho nu => [x, y, d, w, c, pi, rho, nu]

def MetricTasteGate_single_carrier_alignment_toEventFlow : MetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (MetricTasteGate_single_carrier_alignment_fields x).map
      MetricTasteGate_single_carrier_alignment_encodeBHist

def MetricTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | x :: y :: d :: w :: c :: pi :: rho :: nu :: [] =>
      some
        (MetricUp.mk
          (MetricTasteGate_single_carrier_alignment_decodeBHist x)
          (MetricTasteGate_single_carrier_alignment_decodeBHist y)
          (MetricTasteGate_single_carrier_alignment_decodeBHist d)
          (MetricTasteGate_single_carrier_alignment_decodeBHist w)
          (MetricTasteGate_single_carrier_alignment_decodeBHist c)
          (MetricTasteGate_single_carrier_alignment_decodeBHist pi)
          (MetricTasteGate_single_carrier_alignment_decodeBHist rho)
          (MetricTasteGate_single_carrier_alignment_decodeBHist nu))
  | _ => none

private theorem MetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MetricUp,
      MetricTasteGate_single_carrier_alignment_fromEventFlow
          (MetricTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk x y d w c pi rho nu =>
      simp only [MetricTasteGate_single_carrier_alignment_toEventFlow,
        MetricTasteGate_single_carrier_alignment_fields,
        MetricTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons, List.map_nil,
        MetricTasteGate_single_carrier_alignment_decode_encode]

private theorem MetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricUp} :
    MetricTasteGate_single_carrier_alignment_toEventFlow x =
        MetricTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          MetricTasteGate_single_carrier_alignment_fromEventFlow
            (MetricTasteGate_single_carrier_alignment_toEventFlow x) :=
        (MetricTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          MetricTasteGate_single_carrier_alignment_fromEventFlow
            (MetricTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg MetricTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := MetricTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem MetricTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : MetricUp,
      MetricTasteGate_single_carrier_alignment_fields x =
          MetricTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk x₁ y₁ d₁ w₁ c₁ pi₁ rho₁ nu₁ =>
      cases y with
      | mk x₂ y₂ d₂ w₂ c₂ pi₂ rho₂ nu₂ =>
          cases hfields
          rfl

instance MetricTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier MetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MetricTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MetricTasteGate_single_carrier_alignment_fromEventFlow

instance MetricTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate MetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MetricTasteGate_single_carrier_alignment_fromEventFlow
          (MetricTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact MetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance MetricTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful MetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := MetricTasteGate_single_carrier_alignment_fields
  field_faithful := MetricTasteGate_single_carrier_alignment_field_faithful

instance MetricTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial MetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetricTasteGate_single_carrier_alignment :
    (forall x y d w c pi rho nu : BHist,
      MetricTasteGate_single_carrier_alignment_fields
          (MetricUp.mk x y d w c pi rho nu) =
        [x, y, d, w, c, pi, rho, nu]) ∧
      MetricTasteGate_single_carrier_alignment_encodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨(fun _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.MetricUp
