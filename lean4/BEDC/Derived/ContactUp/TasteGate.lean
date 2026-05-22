import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContactUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (manifold form derivative wedge top : BHist) -> ContactUp
  deriving DecidableEq

def ContactTasteGate_single_carrier_alignment_encodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ContactTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: ContactTasteGate_single_carrier_alignment_encodeBHist h

def ContactTasteGate_single_carrier_alignment_decodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (ContactTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (ContactTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ContactTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ContactTasteGate_single_carrier_alignment_decodeBHist
        (ContactTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def ContactTasteGate_single_carrier_alignment_fields : ContactUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContactUp.mk manifold form derivative wedge top =>
      [manifold, form, derivative, wedge, top]

def ContactTasteGate_single_carrier_alignment_toEventFlow : ContactUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (ContactTasteGate_single_carrier_alignment_fields x).map
        ContactTasteGate_single_carrier_alignment_encodeBHist

def ContactTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow -> Option ContactUp
  -- BEDC touchpoint anchor: BHist BMark
  | [manifold, form, derivative, wedge, top] =>
      some
        (ContactUp.mk
          (ContactTasteGate_single_carrier_alignment_decodeBHist manifold)
          (ContactTasteGate_single_carrier_alignment_decodeBHist form)
          (ContactTasteGate_single_carrier_alignment_decodeBHist derivative)
          (ContactTasteGate_single_carrier_alignment_decodeBHist wedge)
          (ContactTasteGate_single_carrier_alignment_decodeBHist top))
  | _ => none

private theorem ContactTasteGate_single_carrier_alignment_round_trip (x : ContactUp) :
    ContactTasteGate_single_carrier_alignment_fromEventFlow
      (ContactTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk manifold form derivative wedge top =>
      change
        some
          (ContactUp.mk
            (ContactTasteGate_single_carrier_alignment_decodeBHist
              (ContactTasteGate_single_carrier_alignment_encodeBHist manifold))
            (ContactTasteGate_single_carrier_alignment_decodeBHist
              (ContactTasteGate_single_carrier_alignment_encodeBHist form))
            (ContactTasteGate_single_carrier_alignment_decodeBHist
              (ContactTasteGate_single_carrier_alignment_encodeBHist derivative))
            (ContactTasteGate_single_carrier_alignment_decodeBHist
              (ContactTasteGate_single_carrier_alignment_encodeBHist wedge))
            (ContactTasteGate_single_carrier_alignment_decodeBHist
              (ContactTasteGate_single_carrier_alignment_encodeBHist top))) =
          some (ContactUp.mk manifold form derivative wedge top)
      rw [ContactTasteGate_single_carrier_alignment_decode_encode manifold,
        ContactTasteGate_single_carrier_alignment_decode_encode form,
        ContactTasteGate_single_carrier_alignment_decode_encode derivative,
        ContactTasteGate_single_carrier_alignment_decode_encode wedge,
        ContactTasteGate_single_carrier_alignment_decode_encode top]

private theorem ContactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContactUp} :
    ContactTasteGate_single_carrier_alignment_toEventFlow x =
        ContactTasteGate_single_carrier_alignment_toEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ContactTasteGate_single_carrier_alignment_fromEventFlow
          (ContactTasteGate_single_carrier_alignment_toEventFlow x) =
        ContactTasteGate_single_carrier_alignment_fromEventFlow
          (ContactTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ContactTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ContactTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContactTasteGate_single_carrier_alignment_fields_faithful
    (x y : ContactUp) :
    ContactTasteGate_single_carrier_alignment_fields x =
        ContactTasteGate_single_carrier_alignment_fields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk manifold₁ form₁ derivative₁ wedge₁ top₁ =>
      cases y with
      | mk manifold₂ form₂ derivative₂ wedge₂ top₂ =>
          injection h with hManifold hRest₁
          injection hRest₁ with hForm hRest₂
          injection hRest₂ with hDerivative hRest₃
          injection hRest₃ with hWedge hRest₄
          injection hRest₄ with hTop _
          subst hManifold
          subst hForm
          subst hDerivative
          subst hWedge
          subst hTop
          rfl

instance contactBHistCarrier : BHistCarrier ContactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ContactTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ContactTasteGate_single_carrier_alignment_fromEventFlow

instance contactChapterTasteGate : ChapterTasteGate ContactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ContactTasteGate_single_carrier_alignment_fromEventFlow
        (ContactTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact ContactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance contactFieldFaithful : FieldFaithful ContactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := ContactTasteGate_single_carrier_alignment_fields
  field_faithful := ContactTasteGate_single_carrier_alignment_fields_faithful

instance contactNontrivial : Nontrivial ContactUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContactUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContactUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ContactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contactChapterTasteGate

theorem ContactTasteGate_single_carrier_alignment :
    (∀ manifold form derivative wedge top : BHist,
      ContactTasteGate_single_carrier_alignment_fields
        (ContactUp.mk manifold form derivative wedge top) =
          [manifold, form, derivative, wedge, top]) ∧
      ContactTasteGate_single_carrier_alignment_encodeBHist (BHist.e1 BHist.Empty) =
        [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro manifold form derivative wedge top
    rfl
  · rfl

end BEDC.Derived.ContactUp
