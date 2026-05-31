import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CutRegularizationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CutRegularizationUp : Type where
  | mk (D L A Delta W S R E H C P N : BHist) : CutRegularizationUp
  deriving DecidableEq

def CutRegularizationTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CutRegularizationTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CutRegularizationTasteGate_single_carrier_alignment_encodeBHist h

def CutRegularizationTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CutRegularizationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
          (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CutRegularizationTasteGate_single_carrier_alignment_toEventFlow :
    CutRegularizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CutRegularizationUp.mk D L A Delta W S R E H C P N =>
      [CutRegularizationTasteGate_single_carrier_alignment_encodeBHist D,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist L,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist A,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist Delta,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist W,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist S,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist R,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist E,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist H,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist C,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist P,
        CutRegularizationTasteGate_single_carrier_alignment_encodeBHist N]

private def CutRegularizationTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CutRegularizationTasteGate_single_carrier_alignment_eventAt index rest

def CutRegularizationTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CutRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CutRegularizationUp.mk
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 0 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 1 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 2 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 3 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 4 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 5 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 6 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 7 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 8 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 9 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 10 ef))
      (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
        (CutRegularizationTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem CutRegularizationTasteGate_single_carrier_alignment_round_trip
    (x : CutRegularizationUp) :
    CutRegularizationTasteGate_single_carrier_alignment_fromEventFlow
        (CutRegularizationTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D L A Delta W S R E H C P N =>
      change
        some
          (CutRegularizationUp.mk
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist D))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist L))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist A))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist Delta))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist W))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist S))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist R))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist E))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist H))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist C))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist P))
            (CutRegularizationTasteGate_single_carrier_alignment_decodeBHist
              (CutRegularizationTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CutRegularizationUp.mk D L A Delta W S R E H C P N)
      rw [CutRegularizationTasteGate_single_carrier_alignment_decode_encode D,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode L,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode A,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode Delta,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode W,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode S,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode R,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode E,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode H,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode C,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode P,
        CutRegularizationTasteGate_single_carrier_alignment_decode_encode N]

private theorem CutRegularizationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CutRegularizationUp} :
    CutRegularizationTasteGate_single_carrier_alignment_toEventFlow x =
        CutRegularizationTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CutRegularizationTasteGate_single_carrier_alignment_fromEventFlow
          (CutRegularizationTasteGate_single_carrier_alignment_toEventFlow x) =
        CutRegularizationTasteGate_single_carrier_alignment_fromEventFlow
          (CutRegularizationTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CutRegularizationTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CutRegularizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CutRegularizationTasteGate_single_carrier_alignment_round_trip y)))

instance cutRegularizationBHistCarrier : BHistCarrier CutRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CutRegularizationTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CutRegularizationTasteGate_single_carrier_alignment_fromEventFlow

theorem CutRegularizationTasteGate_single_carrier_alignment :
    ChapterTasteGate CutRegularizationUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact {
    round_trip := by
      intro x
      change
        CutRegularizationTasteGate_single_carrier_alignment_fromEventFlow
            (CutRegularizationTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
      exact CutRegularizationTasteGate_single_carrier_alignment_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy (CutRegularizationTasteGate_single_carrier_alignment_toEventFlow_injective heq)
  }

end BEDC.Derived.CutRegularizationUp.TasteGate
