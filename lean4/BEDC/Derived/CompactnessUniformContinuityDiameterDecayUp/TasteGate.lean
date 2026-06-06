import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactnessUniformContinuityDiameterDecayUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactnessUniformContinuityDiameterDecayUp : Type where
  | mk (K F M T E H C P N : BHist) : CompactnessUniformContinuityDiameterDecayUp
  deriving DecidableEq

def CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist h

def CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
          (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fields :
    CompactnessUniformContinuityDiameterDecayUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactnessUniformContinuityDiameterDecayUp.mk K F M T E H C P N =>
      [K, F, M, T, E, H, C, P, N]

def CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow :
    CompactnessUniformContinuityDiameterDecayUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fields x).map
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist

private def CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt index rest

def CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CompactnessUniformContinuityDiameterDecayUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactnessUniformContinuityDiameterDecayUp.mk
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 0 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 1 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 2 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 3 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 4 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 5 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 6 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 7 ef))
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_round_trip
    (x : CompactnessUniformContinuityDiameterDecayUp) :
    CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fromEventFlow
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F M T E H C P N =>
      change
        some
          (CompactnessUniformContinuityDiameterDecayUp.mk
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist K))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist F))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist M))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist T))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist E))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist H))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist C))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist P))
            (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decodeBHist
              (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CompactnessUniformContinuityDiameterDecayUp.mk K F M T E H C P N)
      rw [
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode K,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode F,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode M,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode T,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode E,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode H,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode C,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode P,
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactnessUniformContinuityDiameterDecayUp} :
    CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow x =
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fromEventFlow
          (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow x) =
        CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fromEventFlow
          (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_round_trip y)))

instance CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CompactnessUniformContinuityDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow :=
    CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fromEventFlow

instance CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CompactnessUniformContinuityDiameterDecayUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_fromEventFlow
          (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment :
    ChapterTasteGate CompactnessUniformContinuityDiameterDecayUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    CompactnessUniformContinuityDiameterDecayTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.CompactnessUniformContinuityDiameterDecayUp
