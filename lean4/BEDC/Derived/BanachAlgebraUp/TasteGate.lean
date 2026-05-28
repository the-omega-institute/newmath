import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachAlgebraUp : Type where
  | mk
      (ring norm banach productControl completionSeal transport replay provenance localName :
        BHist) :
      BanachAlgebraUp
  deriving DecidableEq

def BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h

def BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BanachAlgebraTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist
          (BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BanachAlgebraTasteGate_single_carrier_alignment_fields :
    BanachAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachAlgebraUp.mk ring norm banach productControl completionSeal transport replay
      provenance localName =>
      [ring, norm, banach, productControl, completionSeal, transport, replay, provenance,
        localName]

def BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow :
    BanachAlgebraUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BanachAlgebraTasteGate_single_carrier_alignment_fields x).map
      BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist

def BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BanachAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | ring :: norm :: banach :: productControl :: completionSeal :: transport :: replay ::
      provenance :: localName :: [] =>
      some
        (BanachAlgebraUp.mk
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist ring)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist norm)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist banach)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist productControl)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist completionSeal)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist transport)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist replay)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist provenance)
          (BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist localName))
  | _ => none

private theorem BanachAlgebraTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachAlgebraUp,
      BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
          (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk ring norm banach productControl completionSeal transport replay provenance localName =>
      simp only [BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow,
        BanachAlgebraTasteGate_single_carrier_alignment_fields,
        BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, BanachAlgebraTasteGate_single_carrier_alignment_decode_encode]

private theorem BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachAlgebraUp} :
    BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x =
        BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
            (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x) :=
        (BanachAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
            (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := BanachAlgebraTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem BanachAlgebraTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BanachAlgebraUp,
      BanachAlgebraTasteGate_single_carrier_alignment_fields x =
          BanachAlgebraTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk ring₁ norm₁ banach₁ productControl₁ completionSeal₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk ring₂ norm₂ banach₂ productControl₂ completionSeal₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance BanachAlgebraTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow

instance BanachAlgebraTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BanachAlgebraTasteGate_single_carrier_alignment_fromEventFlow
          (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BanachAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance BanachAlgebraTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BanachAlgebraTasteGate_single_carrier_alignment_fields
  field_faithful := BanachAlgebraTasteGate_single_carrier_alignment_field_faithful

instance BanachAlgebraTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BanachAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def BanachAlgebraTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate BanachAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BanachAlgebraTasteGate_single_carrier_alignment_ChapterTasteGate

theorem BanachAlgebraTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      BanachAlgebraTasteGate_single_carrier_alignment_decodeBHist
          (BanachAlgebraTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      BanachAlgebraTasteGate_single_carrier_alignment_fields
          (BanachAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨BanachAlgebraTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.BanachAlgebraUp
