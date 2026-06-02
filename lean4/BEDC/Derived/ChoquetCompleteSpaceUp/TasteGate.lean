import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoquetCompleteSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoquetCompleteSpaceUp : Type where
  | mk (G M L S R E H C P N : BHist) : ChoquetCompleteSpaceUp
  deriving DecidableEq

def ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist h

def ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow :
    ChoquetCompleteSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChoquetCompleteSpaceUp.mk G M L S R E H C P N =>
      [ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist G,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist M,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist L,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist S,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist R,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist E,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist H,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist C,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist P,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist N]

def ChoquetCompleteSpaceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option ChoquetCompleteSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | G :: M :: L :: S :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (ChoquetCompleteSpaceUp.mk
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist G)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist M)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist L)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist S)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist R)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist E)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist H)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist C)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist P)
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem ChoquetCompleteSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChoquetCompleteSpaceUp,
      ChoquetCompleteSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk G M L S R E H C P N =>
      change
        some
            (ChoquetCompleteSpaceUp.mk
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist G))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist M))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist L))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist S))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist R))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist E))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist H))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist C))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist P))
              (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
                (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (ChoquetCompleteSpaceUp.mk G M L S R E H C P N)
      rw [ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode G,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode M,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode L,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode S,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode R,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode E,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode H,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode C,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode P,
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ChoquetCompleteSpaceUp} :
    ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow x =
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      ChoquetCompleteSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow x) =
        ChoquetCompleteSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg ChoquetCompleteSpaceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance ChoquetCompleteSpaceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier ChoquetCompleteSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := ChoquetCompleteSpaceTasteGate_single_carrier_alignment_fromEventFlow

instance ChoquetCompleteSpaceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate ChoquetCompleteSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      ChoquetCompleteSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact ChoquetCompleteSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ChoquetCompleteSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      ChoquetCompleteSpaceTasteGate_single_carrier_alignment_decodeBHist
          (ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
      ChoquetCompleteSpaceTasteGate_single_carrier_alignment_encodeBHist BHist.Empty =
        ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.ChoquetCompleteSpaceUp
