import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RepresentationRingUp : Type where
  | mk (G R V S T P rho lambda : BHist) : RepresentationRingUp
  deriving DecidableEq

def RepresentationRingTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def RepresentationRingTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: RepresentationRingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: RepresentationRingTasteGate_single_carrier_alignment_encodeBHist h

def RepresentationRingTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RepresentationRingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
          (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RepresentationRingTasteGate_single_carrier_alignment_fields :
    RepresentationRingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RepresentationRingUp.mk G R V S T P rho lambda => [G, R, V, S, T, P, rho, lambda]

def RepresentationRingTasteGate_single_carrier_alignment_toEventFlow :
    RepresentationRingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RepresentationRingUp.mk G R V S T P rho lambda =>
      [RepresentationRingTasteGate_single_carrier_alignment_tag,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist G,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist R,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist V,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist S,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist T,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist P,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist rho,
        RepresentationRingTasteGate_single_carrier_alignment_encodeBHist lambda]

private def RepresentationRingTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RepresentationRingTasteGate_single_carrier_alignment_eventAt index rest

def RepresentationRingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RepresentationRingUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RepresentationRingUp.mk
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 1 ef))
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 2 ef))
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 3 ef))
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 4 ef))
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 5 ef))
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 6 ef))
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 7 ef))
          (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
            (RepresentationRingTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem RepresentationRingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RepresentationRingUp,
      RepresentationRingTasteGate_single_carrier_alignment_fromEventFlow
          (RepresentationRingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G R V S T P rho lambda =>
      change
        some
          (RepresentationRingUp.mk
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist G))
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist R))
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist V))
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist S))
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist T))
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist P))
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist rho))
            (RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
              (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist lambda))) =
          some (RepresentationRingUp.mk G R V S T P rho lambda)
      rw [RepresentationRingTasteGate_single_carrier_alignment_decode G,
        RepresentationRingTasteGate_single_carrier_alignment_decode R,
        RepresentationRingTasteGate_single_carrier_alignment_decode V,
        RepresentationRingTasteGate_single_carrier_alignment_decode S,
        RepresentationRingTasteGate_single_carrier_alignment_decode T,
        RepresentationRingTasteGate_single_carrier_alignment_decode P,
        RepresentationRingTasteGate_single_carrier_alignment_decode rho,
        RepresentationRingTasteGate_single_carrier_alignment_decode lambda]

private theorem RepresentationRingTasteGate_single_carrier_alignment_injective
    {x y : RepresentationRingUp} :
    RepresentationRingTasteGate_single_carrier_alignment_toEventFlow x =
        RepresentationRingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RepresentationRingTasteGate_single_carrier_alignment_fromEventFlow
          (RepresentationRingTasteGate_single_carrier_alignment_toEventFlow x) =
        RepresentationRingTasteGate_single_carrier_alignment_fromEventFlow
          (RepresentationRingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RepresentationRingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RepresentationRingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RepresentationRingTasteGate_single_carrier_alignment_round_trip y)))

private theorem RepresentationRingTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RepresentationRingUp,
      RepresentationRingTasteGate_single_carrier_alignment_fields x =
          RepresentationRingTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ R₁ V₁ S₁ T₁ P₁ rho₁ lambda₁ =>
      cases y with
      | mk G₂ R₂ V₂ S₂ T₂ P₂ rho₂ lambda₂ =>
          cases hfields
          rfl

instance RepresentationRingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RepresentationRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RepresentationRingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RepresentationRingTasteGate_single_carrier_alignment_fromEventFlow

instance RepresentationRingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RepresentationRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RepresentationRingTasteGate_single_carrier_alignment_fromEventFlow
          (RepresentationRingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RepresentationRingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RepresentationRingTasteGate_single_carrier_alignment_injective heq)

instance RepresentationRingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RepresentationRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RepresentationRingTasteGate_single_carrier_alignment_fields
  field_faithful := RepresentationRingTasteGate_single_carrier_alignment_fields_faithful

instance RepresentationRingTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial RepresentationRingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RepresentationRingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RepresentationRingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RepresentationRingTasteGate_single_carrier_alignment :
    (forall h : BHist,
      RepresentationRingTasteGate_single_carrier_alignment_decodeBHist
        (RepresentationRingTasteGate_single_carrier_alignment_encodeBHist h) = h) /\
      RepresentationRingTasteGate_single_carrier_alignment_fields
        (RepresentationRingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty] /\
        RepresentationRingTasteGate_single_carrier_alignment_toEventFlow
          (RepresentationRingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RepresentationRingTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.RepresentationRingUp
