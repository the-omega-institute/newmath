import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VitaliCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VitaliCoverUp : Type where
  | mk (I D E F M R H C P N : BHist) : VitaliCoverUp
  deriving DecidableEq

def vitaliCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: vitaliCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: vitaliCoverEncodeBHist h

def vitaliCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (vitaliCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (vitaliCoverDecodeBHist tail)

private theorem VitaliCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, vitaliCoverDecodeBHist (vitaliCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def vitaliCoverFields : VitaliCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VitaliCoverUp.mk I D E F M R H C P N => [I, D, E, F, M, R, H, C, P, N]

def vitaliCoverToEventFlow : VitaliCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | VitaliCoverUp.mk I D E F M R H C P N =>
      [[BMark.b0, BMark.b1, BMark.b0, BMark.b1],
        vitaliCoverEncodeBHist I,
        vitaliCoverEncodeBHist D,
        vitaliCoverEncodeBHist E,
        vitaliCoverEncodeBHist F,
        vitaliCoverEncodeBHist M,
        vitaliCoverEncodeBHist R,
        vitaliCoverEncodeBHist H,
        vitaliCoverEncodeBHist C,
        vitaliCoverEncodeBHist P,
        vitaliCoverEncodeBHist N]

def vitaliCoverFromEventFlow : EventFlow → Option VitaliCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, I, D, E, F, M, R, H, C, P, N] =>
      match tag with
      | [BMark.b0, BMark.b1, BMark.b0, BMark.b1] =>
          some
            (VitaliCoverUp.mk
              (vitaliCoverDecodeBHist I)
              (vitaliCoverDecodeBHist D)
              (vitaliCoverDecodeBHist E)
              (vitaliCoverDecodeBHist F)
              (vitaliCoverDecodeBHist M)
              (vitaliCoverDecodeBHist R)
              (vitaliCoverDecodeBHist H)
              (vitaliCoverDecodeBHist C)
              (vitaliCoverDecodeBHist P)
              (vitaliCoverDecodeBHist N))
      | _ => none
  | _ => none

private theorem VitaliCoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : VitaliCoverUp,
      vitaliCoverFromEventFlow (vitaliCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D E F M R H C P N =>
      change
        some
            (VitaliCoverUp.mk
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist I))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist D))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist E))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist F))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist M))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist R))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist H))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist C))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist P))
              (vitaliCoverDecodeBHist (vitaliCoverEncodeBHist N))) =
          some (VitaliCoverUp.mk I D E F M R H C P N)
      rw [VitaliCoverTasteGate_single_carrier_alignment_decode_encode I,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode D,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode E,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode F,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode M,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode R,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode H,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode C,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode P,
        VitaliCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem VitaliCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VitaliCoverUp} :
    vitaliCoverToEventFlow x = vitaliCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      vitaliCoverFromEventFlow (vitaliCoverToEventFlow x) =
        vitaliCoverFromEventFlow (vitaliCoverToEventFlow y) :=
    congrArg vitaliCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (VitaliCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (VitaliCoverTasteGate_single_carrier_alignment_round_trip y)))

private theorem VitaliCoverTasteGate_single_carrier_alignment_fields :
    ∀ x y : VitaliCoverUp, vitaliCoverFields x = vitaliCoverFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 D1 E1 F1 M1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 D2 E2 F2 M2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance vitaliCoverBHistCarrier : BHistCarrier VitaliCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := vitaliCoverToEventFlow
  fromEventFlow := vitaliCoverFromEventFlow

instance vitaliCoverChapterTasteGate : ChapterTasteGate VitaliCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change vitaliCoverFromEventFlow (vitaliCoverToEventFlow x) = some x
    exact VitaliCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (VitaliCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance vitaliCoverFieldFaithful : FieldFaithful VitaliCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := vitaliCoverFields
  field_faithful := VitaliCoverTasteGate_single_carrier_alignment_fields

instance vitaliCoverNontrivial : Nontrivial VitaliCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨VitaliCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      VitaliCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate VitaliCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  vitaliCoverChapterTasteGate

theorem VitaliCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, vitaliCoverDecodeBHist (vitaliCoverEncodeBHist h) = h) ∧
      vitaliCoverFields
          (VitaliCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        vitaliCoverToEventFlow
            (VitaliCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b0, BMark.b1, BMark.b0, BMark.b1], [], [], [], [], [], [], [], [], [],
            []] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨VitaliCoverTasteGate_single_carrier_alignment_decode_encode, rfl, rfl⟩

end BEDC.Derived.VitaliCoverUp
