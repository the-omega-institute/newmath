import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalSpaceUp : Type where
  | mk (T F0 F1 D U0 U1 H K P L : BHist) : NormalSpaceUp
  deriving DecidableEq

def NormalSpaceTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: NormalSpaceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: NormalSpaceTasteGate_single_carrier_alignment_encodeBHist h

def NormalSpaceTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem NormalSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      NormalSpaceTasteGate_single_carrier_alignment_decodeBHist
          (NormalSpaceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def NormalSpaceTasteGate_single_carrier_alignment_fields : NormalSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalSpaceUp.mk T F0 F1 D U0 U1 H K P L => [T, F0, F1, D, U0, U1, H, K, P, L]

def NormalSpaceTasteGate_single_carrier_alignment_toEventFlow : NormalSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (NormalSpaceTasteGate_single_carrier_alignment_fields x).map
      NormalSpaceTasteGate_single_carrier_alignment_encodeBHist

def NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option NormalSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | T :: F0 :: F1 :: D :: U0 :: U1 :: H :: K :: P :: L :: [] =>
      some
        (NormalSpaceUp.mk
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist T)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist F0)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist F1)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist D)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist U0)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist U1)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist H)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist K)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist P)
          (NormalSpaceTasteGate_single_carrier_alignment_decodeBHist L))
  | _ => none

private theorem NormalSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NormalSpaceUp,
      NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (NormalSpaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk T F0 F1 D U0 U1 H K P L =>
      simp only [NormalSpaceTasteGate_single_carrier_alignment_toEventFlow,
        NormalSpaceTasteGate_single_carrier_alignment_fields,
        NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, NormalSpaceTasteGate_single_carrier_alignment_decode_encode]

private theorem NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NormalSpaceUp} :
    NormalSpaceTasteGate_single_carrier_alignment_toEventFlow x =
        NormalSpaceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow
            (NormalSpaceTasteGate_single_carrier_alignment_toEventFlow x) :=
        (NormalSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow
            (NormalSpaceTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := NormalSpaceTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem NormalSpaceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : NormalSpaceUp,
      NormalSpaceTasteGate_single_carrier_alignment_fields x =
          NormalSpaceTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 F01 F11 D1 U01 U11 H1 K1 P1 L1 =>
      cases y with
      | mk T2 F02 F12 D2 U02 U12 H2 K2 P2 L2 =>
          cases hfields
          rfl

instance NormalSpaceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := NormalSpaceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow

instance NormalSpaceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      NormalSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (NormalSpaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact NormalSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance NormalSpaceTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := NormalSpaceTasteGate_single_carrier_alignment_fields
  field_faithful := NormalSpaceTasteGate_single_carrier_alignment_field_faithful

instance NormalSpaceTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NormalSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NormalSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def NormalSpaceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate NormalSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  NormalSpaceTasteGate_single_carrier_alignment_ChapterTasteGate

theorem NormalSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      NormalSpaceTasteGate_single_carrier_alignment_decodeBHist
          (NormalSpaceTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      NormalSpaceTasteGate_single_carrier_alignment_fields
          (NormalSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨NormalSpaceTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.NormalSpaceUp.TasteGate
