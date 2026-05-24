import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionEndpointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionEndpointUp : Type where
  | mk (B L X U R H C P N : BHist) : RegularCauchyCompletionEndpointUp
  deriving DecidableEq

def RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_encodeBHist h

def RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_encodeBHist h) =
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

def RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fields :
    RegularCauchyCompletionEndpointUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionEndpointUp.mk B L X U R H C P N => [B, L, X, U, R, H, C, P, N]

def RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow :
    RegularCauchyCompletionEndpointUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    [BMark.b1] ::
      (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fields x).map
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_encodeBHist

def RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegularCauchyCompletionEndpointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [BMark.b1] :: B :: L :: X :: U :: R :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyCompletionEndpointUp.mk
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist B)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist L)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist X)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist U)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist R)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist H)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist C)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist P)
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCompletionEndpointUp,
      RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B L X U R H C P N =>
      simp only [RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fields,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow,
        List.map_cons, List.map_nil,
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode]

private theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompletionEndpointUp} :
    RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow x =
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow
            (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow x) :=
        (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow
            (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg
          RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y :=
        RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RegularCauchyCompletionEndpointUp,
      RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fields x =
          RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ L₁ X₁ U₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ L₂ X₂ U₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow

instance RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fields
  field_faithful :=
    RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_field_faithful

instance RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial RegularCauchyCompletionEndpointUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionEndpointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyCompletionEndpointUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyCompletionEndpointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_ChapterTasteGate

theorem RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decodeBHist
          (RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_fields
          (RegularCauchyCompletionEndpointUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] ∧
      RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_toEventFlow
          (RegularCauchyCompletionEndpointUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact ⟨RegularCauchyCompletionEndpointTasteGate_single_carrier_alignment_decode_encode,
    rfl, rfl⟩

end BEDC.Derived.RegularCauchyCompletionEndpointUp
