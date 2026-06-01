import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformSpaceUp : Type where
  | mk (R Q W D M E H C P N : BHist) : RealUniformSpaceUp

private def RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist h

private def RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
          (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow :
    RealUniformSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformSpaceUp.mk R Q W D M E H C P N =>
      [RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist R,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist Q,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist W,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist D,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist M,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist E,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist H,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist C,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist P,
        RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist N]

private def RealUniformSpaceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealUniformSpaceTasteGate_single_carrier_alignment_eventAt index rest

private def RealUniformSpaceTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option RealUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealUniformSpaceUp.mk
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 8 ef))
      (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
        (RealUniformSpaceTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem RealUniformSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealUniformSpaceUp,
      RealUniformSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q W D M E H C P N =>
      change
        some
          (RealUniformSpaceUp.mk
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist R))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist Q))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist W))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist D))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist M))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist E))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist H))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist C))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist P))
            (RealUniformSpaceTasteGate_single_carrier_alignment_decodeBHist
              (RealUniformSpaceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (RealUniformSpaceUp.mk R Q W D M E H C P N)
      rw [RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode R,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode W,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode D,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode M,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode E,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode H,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode C,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode P,
        RealUniformSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealUniformSpaceUp} :
    RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow x =
        RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RealUniformSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow x) =
        RealUniformSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RealUniformSpaceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealUniformSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealUniformSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance realUniformSpaceBHistCarrier : BHistCarrier RealUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := RealUniformSpaceTasteGate_single_carrier_alignment_fromEventFlow

instance realUniformSpaceChapterTasteGate : ChapterTasteGate RealUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RealUniformSpaceTasteGate_single_carrier_alignment_fromEventFlow
          (RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RealUniformSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealUniformSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformSpaceChapterTasteGate

theorem RealUniformSpaceTasteGate_single_carrier_alignment :
    ChapterTasteGate RealUniformSpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact realUniformSpaceChapterTasteGate

end BEDC.Derived.RealUniformSpaceUp
