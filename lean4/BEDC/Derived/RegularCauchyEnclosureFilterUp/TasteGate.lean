import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyEnclosureFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyEnclosureFilterUp : Type where
  | mk (W D Q F B R H C P N : BHist) : RegularCauchyEnclosureFilterUp
  deriving DecidableEq

def RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist h

def RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow :
    RegularCauchyEnclosureFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyEnclosureFilterUp.mk W D Q F B R H C P N =>
      [RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist W,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist D,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist Q,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist F,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist B,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist R,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist H,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist C,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist P,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist N]

def RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RegularCauchyEnclosureFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | W :: D :: Q :: F :: B :: R :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyEnclosureFilterUp.mk
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist W)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist D)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist Q)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist F)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist B)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist R)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist H)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist C)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist P)
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyEnclosureFilterUp,
      RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk W D Q F B R H C P N =>
      change
        some
            (RegularCauchyEnclosureFilterUp.mk
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist W))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist D))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist Q))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist F))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist B))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist R))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist H))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist C))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist P))
              (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
                (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RegularCauchyEnclosureFilterUp.mk W D Q F B R H C P N)
      rw [RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode F,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyEnclosureFilterUp} :
    RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow x =
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow x) =
        RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_round_trip y)))

instance RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier RegularCauchyEnclosureFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_fromEventFlow

instance RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate RegularCauchyEnclosureFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_fromEventFlow
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_decodeBHist
          (RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      RegularCauchyEnclosureFilterTasteGate_single_carrier_alignment_encodeBHist
          BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.RegularCauchyEnclosureFilterUp
