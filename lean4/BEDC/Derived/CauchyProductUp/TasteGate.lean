import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductUp : Type where
  | mk
      (sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
        classifier transport routes ledger name : BHist) :
      CauchyProductUp
  deriving DecidableEq

def CauchyProductTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyProductTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyProductTasteGate_single_carrier_alignment_encodeBHist h

def CauchyProductTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CauchyProductTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CauchyProductTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyProductTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyProductTasteGate_single_carrier_alignment_decodeBHist
          (CauchyProductTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyProductTasteGate_single_carrier_alignment_fields : CauchyProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductUp.mk sourceA sourceB windowA windowB radiusA radiusB observationA
      observationB product classifier transport routes ledger name =>
      [sourceA, sourceB, windowA, windowB, radiusA, radiusB, observationA, observationB,
        product, classifier, transport, routes, ledger, name]

def CauchyProductTasteGate_single_carrier_alignment_toEventFlow :
    CauchyProductUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyProductTasteGate_single_carrier_alignment_fields x).map
      CauchyProductTasteGate_single_carrier_alignment_encodeBHist

def CauchyProductTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | sourceA :: sourceB :: windowA :: windowB :: radiusA :: radiusB :: observationA ::
      observationB :: product :: classifier :: transport :: routes :: ledger :: name :: [] =>
      some
        (CauchyProductUp.mk
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist sourceA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist sourceB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist windowA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist windowB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist radiusA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist radiusB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist observationA)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist observationB)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist product)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist classifier)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist transport)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist routes)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist ledger)
          (CauchyProductTasteGate_single_carrier_alignment_decodeBHist name))
  | _ => none

private theorem CauchyProductTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyProductUp,
      CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name =>
      simp only [CauchyProductTasteGate_single_carrier_alignment_toEventFlow,
        CauchyProductTasteGate_single_carrier_alignment_fields,
        CauchyProductTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, CauchyProductTasteGate_single_carrier_alignment_decode_encode]

private theorem CauchyProductTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyProductUp} :
    CauchyProductTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyProductTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyProductTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CauchyProductTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyProductTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CauchyProductTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := CauchyProductTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem CauchyProductTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyProductUp,
      CauchyProductTasteGate_single_carrier_alignment_fields x =
          CauchyProductTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sourceA₁ sourceB₁ windowA₁ windowB₁ radiusA₁ radiusB₁ observationA₁ observationB₁
      product₁ classifier₁ transport₁ routes₁ ledger₁ name₁ =>
      cases y with
      | mk sourceA₂ sourceB₂ windowA₂ windowB₂ radiusA₂ radiusB₂ observationA₂ observationB₂
          product₂ classifier₂ transport₂ routes₂ ledger₂ name₂ =>
          cases hfields
          rfl

instance CauchyProductTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyProductTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyProductTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyProductTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyProductTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyProductTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyProductTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyProductTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CauchyProductTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyProductTasteGate_single_carrier_alignment_fields
  field_faithful := CauchyProductTasteGate_single_carrier_alignment_field_faithful

instance CauchyProductTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial CauchyProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyProductUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyProductTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyProductTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CauchyProductTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CauchyProductTasteGate_single_carrier_alignment_decodeBHist
          (CauchyProductTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CauchyProductTasteGate_single_carrier_alignment_fields
          (CauchyProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨CauchyProductTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CauchyProductUp
