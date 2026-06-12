import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WLPOBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WLPOBoundaryUp : Type where
  | mk (B S R E Q H C P N : BHist) : WLPOBoundaryUp
  deriving DecidableEq

def WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist h

def WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
          (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def WLPOBoundaryTasteGate_single_carrier_alignment_fields :
    WLPOBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WLPOBoundaryUp.mk B S R E Q H C P N =>
      [B, S, R, E, Q, H, C, P, N]

def WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow :
    WLPOBoundaryUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (WLPOBoundaryTasteGate_single_carrier_alignment_fields x).map
      WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist

private def WLPOBoundaryTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      WLPOBoundaryTasteGate_single_carrier_alignment_eventAt index rest

def WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option WLPOBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WLPOBoundaryUp.mk
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 0 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 1 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 2 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 3 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 4 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 5 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 6 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 7 ef))
      (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
        (WLPOBoundaryTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem WLPOBoundaryTasteGate_single_carrier_alignment_round_trip
    (x : WLPOBoundaryUp) :
    WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow
        (WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B S R E Q H C P N =>
      change
        some
            (WLPOBoundaryUp.mk
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist B))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist S))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist R))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist E))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist Q))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist H))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist C))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist P))
              (WLPOBoundaryTasteGate_single_carrier_alignment_decodeBHist
                (WLPOBoundaryTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (WLPOBoundaryUp.mk B S R E Q H C P N)
      rw [WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode B,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode S,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode R,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode E,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode Q,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode H,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode C,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode P,
        WLPOBoundaryTasteGate_single_carrier_alignment_decode_encode N]

private theorem WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WLPOBoundaryUp} :
    WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow x =
        WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WLPOBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WLPOBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance wlpoBoundaryBHistCarrier : BHistCarrier WLPOBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow

instance wlpoBoundaryChapterTasteGate : ChapterTasteGate WLPOBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow
          (WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact WLPOBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem WLPOBoundaryTasteGate_single_carrier_alignment :
    ChapterTasteGate WLPOBoundaryUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact {
    round_trip := by
      intro x
      change
        WLPOBoundaryTasteGate_single_carrier_alignment_fromEventFlow
            (WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow x) =
          some x
      exact WLPOBoundaryTasteGate_single_carrier_alignment_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy (WLPOBoundaryTasteGate_single_carrier_alignment_toEventFlow_injective heq)
  }

end BEDC.Derived.WLPOBoundaryUp
