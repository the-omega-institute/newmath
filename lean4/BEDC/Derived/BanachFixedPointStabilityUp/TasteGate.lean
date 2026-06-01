import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachFixedPointStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachFixedPointStabilityUp : Type where
  | mk (F I T M Q R E H C P N : BHist) : BanachFixedPointStabilityUp
  deriving DecidableEq

def BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist h

def BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow :
    BanachFixedPointStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BanachFixedPointStabilityUp.mk F I T M Q R E H C P N =>
      [BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist F,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist I,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist T,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist M,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist Q,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist R,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist E,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist H,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist C,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist P,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist N]

def BanachFixedPointStabilityTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BanachFixedPointStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: I :: T :: M :: Q :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (BanachFixedPointStabilityUp.mk
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist F)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist I)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist T)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist M)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist Q)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist R)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist E)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist H)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist C)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist P)
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem BanachFixedPointStabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachFixedPointStabilityUp,
      BanachFixedPointStabilityTasteGate_single_carrier_alignment_fromEventFlow
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk F I T M Q R E H C P N =>
      change
        some
            (BanachFixedPointStabilityUp.mk
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist F))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist I))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist T))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist M))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist Q))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist R))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist E))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist H))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist C))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist P))
              (BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
                (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (BanachFixedPointStabilityUp.mk F I T M Q R E H C P N)
      rw [BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode F,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode I,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode T,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode M,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode Q,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode R,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode E,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode H,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode C,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode P,
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_decode_encode N]

private theorem BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachFixedPointStabilityUp} :
    BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow x =
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BanachFixedPointStabilityTasteGate_single_carrier_alignment_fromEventFlow
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow x) =
        BanachFixedPointStabilityTasteGate_single_carrier_alignment_fromEventFlow
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BanachFixedPointStabilityTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BanachFixedPointStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BanachFixedPointStabilityTasteGate_single_carrier_alignment_round_trip y)))

instance BanachFixedPointStabilityTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BanachFixedPointStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BanachFixedPointStabilityTasteGate_single_carrier_alignment_fromEventFlow

instance BanachFixedPointStabilityTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BanachFixedPointStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BanachFixedPointStabilityTasteGate_single_carrier_alignment_fromEventFlow
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BanachFixedPointStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BanachFixedPointStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BanachFixedPointStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      BanachFixedPointStabilityTasteGate_single_carrier_alignment_decodeBHist
          (BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      BanachFixedPointStabilityTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.BanachFixedPointStabilityUp
