import BEDC.Derived.DyadicCauchyCriterionUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCauchyCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist h

def DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist,
      DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DyadicCauchyCriterionTasteGate_single_carrier_alignment_fields :
    DyadicCauchyCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCauchyCriterionUp.mk D W T R E H C P N => [D, W, T, R, E, H, C, P, N]

def DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow :
    DyadicCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (DyadicCauchyCriterionTasteGate_single_carrier_alignment_fields x).map
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist

def DyadicCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DyadicCauchyCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: W :: T :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (DyadicCauchyCriterionUp.mk
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist D)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist W)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist T)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist R)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist E)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist H)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist C)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist P)
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem DyadicCauchyCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicCauchyCriterionUp,
      DyadicCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W T R E H C P N =>
      change
        some
          (DyadicCauchyCriterionUp.mk
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist D))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist W))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist T))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist R))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist E))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist H))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist C))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist P))
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
              (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (DyadicCauchyCriterionUp.mk D W T R E H C P N)
      rw [DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist D,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist W,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist T,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist R,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist E,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist H,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist C,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist P,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist N]

private theorem DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicCauchyCriterionUp} :
    DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x =
      DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DyadicCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DyadicCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance DyadicCauchyCriterionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DyadicCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DyadicCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow

instance DyadicCauchyCriterionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DyadicCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DyadicCauchyCriterionTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DyadicCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def DyadicCauchyCriterionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate DyadicCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DyadicCauchyCriterionTasteGate_single_carrier_alignment_ChapterTasteGate

theorem DyadicCauchyCriterionTasteGate_single_carrier_alignment :
    (forall D W T R E H C P N : BHist,
      DyadicCauchyCriterionTasteGate_single_carrier_alignment_fields
          (DyadicCauchyCriterionUp.mk D W T R E H C P N) =
        [D, W, T, R, E, H, C, P, N]) ∧
      (forall h : BHist,
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_decodeBHist
            (DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        DyadicCauchyCriterionTasteGate_single_carrier_alignment_encodeBHist
            (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨(fun _ _ _ _ _ _ _ _ _ => rfl),
      DyadicCauchyCriterionTasteGate_single_carrier_alignment_decode_encode_bhist, rfl⟩

end BEDC.Derived.DyadicCauchyCriterionUp
