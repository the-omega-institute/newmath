import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerFixedPointMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerFixedPointMetricUp : Type where
  | mk (K X M G E R H C P N : BHist) : BrouwerFixedPointMetricUp
  deriving DecidableEq

def brouwerFixedPointMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerFixedPointMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerFixedPointMetricEncodeBHist h

def brouwerFixedPointMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerFixedPointMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerFixedPointMetricDecodeBHist tail)

private theorem BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def brouwerFixedPointMetricFields : BrouwerFixedPointMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerFixedPointMetricUp.mk K X M G E R H C P N => [K, X, M, G, E, R, H, C, P, N]

def brouwerFixedPointMetricToEventFlow : BrouwerFixedPointMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (brouwerFixedPointMetricFields x).map brouwerFixedPointMetricEncodeBHist

private def brouwerFixedPointMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerFixedPointMetricEventAtDefault index rest

def brouwerFixedPointMetricFromEventFlow (ef : EventFlow) : Option BrouwerFixedPointMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerFixedPointMetricUp.mk
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 0 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 1 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 2 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 3 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 4 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 5 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 6 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 7 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 8 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 9 ef)))

private theorem BrouwerFixedPointMetricTasteGate_single_carrier_alignment_round_trip
    (x : BrouwerFixedPointMetricUp) :
    brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K X M G E R H C P N =>
      change
        some
          (BrouwerFixedPointMetricUp.mk
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist K))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist X))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist M))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist G))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist E))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist R))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist H))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist C))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist P))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist N))) =
          some (BrouwerFixedPointMetricUp.mk K X M G E R H C P N)
      rw [BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode K,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode X,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode M,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode G,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode E,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode R,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode H,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode C,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode P,
        BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem BrouwerFixedPointMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BrouwerFixedPointMetricUp} :
    brouwerFixedPointMetricToEventFlow x = brouwerFixedPointMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow x) =
        brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow y) :=
    congrArg brouwerFixedPointMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BrouwerFixedPointMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BrouwerFixedPointMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem BrouwerFixedPointMetricTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BrouwerFixedPointMetricUp,
      brouwerFixedPointMetricFields x = brouwerFixedPointMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ X₁ M₁ G₁ E₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ X₂ M₂ G₂ E₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance brouwerFixedPointMetricBHistCarrier : BHistCarrier BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerFixedPointMetricToEventFlow
  fromEventFlow := brouwerFixedPointMetricFromEventFlow

instance brouwerFixedPointMetricChapterTasteGate :
    ChapterTasteGate BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow x) = some x
    exact BrouwerFixedPointMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BrouwerFixedPointMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance brouwerFixedPointMetricFieldFaithful : FieldFaithful BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := brouwerFixedPointMetricFields
  field_faithful := BrouwerFixedPointMetricTasteGate_single_carrier_alignment_fields_faithful

instance brouwerFixedPointMetricNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BrouwerFixedPointMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BrouwerFixedPointMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BrouwerFixedPointMetricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BrouwerFixedPointMetricUp) ∧
      Nonempty (FieldFaithful BrouwerFixedPointMetricUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial BrouwerFixedPointMetricUp) ∧
          (∀ h : BHist,
            brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist h) = h) ∧
            (∀ x : BrouwerFixedPointMetricUp,
              brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow x) =
                some x) ∧
              brouwerFixedPointMetricEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨brouwerFixedPointMetricChapterTasteGate⟩,
      ⟨brouwerFixedPointMetricFieldFaithful⟩,
      ⟨brouwerFixedPointMetricNontrivial⟩,
      BrouwerFixedPointMetricTasteGate_single_carrier_alignment_decode_encode,
      BrouwerFixedPointMetricTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.BrouwerFixedPointMetricUp
