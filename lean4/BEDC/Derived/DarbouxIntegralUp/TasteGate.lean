import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxIntegralUp : Type where
  | mk (partition upper lower upperSum lowerSum gap realHandoff transports routes name : BHist) :
      DarbouxIntegralUp
  deriving DecidableEq

def DarbouxIntegralTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DarbouxIntegralTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DarbouxIntegralTasteGate_single_carrier_alignment_encodeBHist h

def DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DarbouxIntegralTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist
          (DarbouxIntegralTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DarbouxIntegralTasteGate_single_carrier_alignment_fields :
    DarbouxIntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxIntegralUp.mk partition upper lower upperSum lowerSum gap realHandoff transports routes
      name =>
      [partition, upper, lower, upperSum, lowerSum, gap, realHandoff, transports, routes, name]

def DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow :
    DarbouxIntegralUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (DarbouxIntegralTasteGate_single_carrier_alignment_fields x).map
      DarbouxIntegralTasteGate_single_carrier_alignment_encodeBHist

def DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DarbouxIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | partition :: upper :: lower :: upperSum :: lowerSum :: gap :: realHandoff :: transports ::
      routes :: name :: [] =>
      some
        (DarbouxIntegralUp.mk
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist partition)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist upper)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist lower)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist upperSum)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist lowerSum)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist gap)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist realHandoff)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist transports)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist routes)
          (DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist name))
  | _ => none

private theorem DarbouxIntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DarbouxIntegralUp,
      DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow
          (DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk partition upper lower upperSum lowerSum gap realHandoff transports routes name =>
      simp only [DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow,
        DarbouxIntegralTasteGate_single_carrier_alignment_fields,
        DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, DarbouxIntegralTasteGate_single_carrier_alignment_decode_encode]

private theorem DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DarbouxIntegralUp} :
    DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow x =
        DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow
            (DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow x) :=
        (DarbouxIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow
            (DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := DarbouxIntegralTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem DarbouxIntegralTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : DarbouxIntegralUp,
      DarbouxIntegralTasteGate_single_carrier_alignment_fields x =
          DarbouxIntegralTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk partition₁ upper₁ lower₁ upperSum₁ lowerSum₁ gap₁ realHandoff₁ transports₁ routes₁
      name₁ =>
      cases y with
      | mk partition₂ upper₂ lower₂ upperSum₂ lowerSum₂ gap₂ realHandoff₂ transports₂ routes₂
          name₂ =>
          cases hfields
          rfl

instance DarbouxIntegralTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DarbouxIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow

instance DarbouxIntegralTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DarbouxIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DarbouxIntegralTasteGate_single_carrier_alignment_fromEventFlow
          (DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DarbouxIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance DarbouxIntegralTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful DarbouxIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DarbouxIntegralTasteGate_single_carrier_alignment_fields
  field_faithful := DarbouxIntegralTasteGate_single_carrier_alignment_field_faithful

instance DarbouxIntegralTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial DarbouxIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DarbouxIntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DarbouxIntegralUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def DarbouxIntegralTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DarbouxIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DarbouxIntegralTasteGate_single_carrier_alignment_ChapterTasteGate

theorem DarbouxIntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      DarbouxIntegralTasteGate_single_carrier_alignment_decodeBHist
          (DarbouxIntegralTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      DarbouxIntegralTasteGate_single_carrier_alignment_fields
          (DarbouxIntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨DarbouxIntegralTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.DarbouxIntegralUp
