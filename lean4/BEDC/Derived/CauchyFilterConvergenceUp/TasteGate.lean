import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterConvergenceUp : Type where
  | mk (F B M S D R E W H C P N : BHist) : CauchyFilterConvergenceUp
  deriving DecidableEq

def CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist h

def CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyFilterConvergenceTasteGate_single_carrier_alignment_fields :
    CauchyFilterConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterConvergenceUp.mk F B M S D R E W H C P N =>
      [F, B, M, S, D, R, E, W, H, C, P, N]

def CauchyFilterConvergenceTasteGate_single_carrier_alignment_tag : Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0 => [BMark.b0]
  | 1 => [BMark.b1, BMark.b0]
  | 2 => [BMark.b1, BMark.b1, BMark.b0]
  | 3 => [BMark.b1, BMark.b1, BMark.b1, BMark.b0]
  | 4 => [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]
  | 5 => [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]
  | 6 => [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]
  | 7 =>
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b0]
  | 8 =>
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b0]
  | 9 =>
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b1, BMark.b0]
  | 10 =>
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b1, BMark.b1, BMark.b0]
  | _ =>
      [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
        BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]

def CauchyFilterConvergenceTasteGate_single_carrier_alignment_pairRows :
    Nat → List BHist → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | _index, [] => []
  | index, row :: rest =>
      CauchyFilterConvergenceTasteGate_single_carrier_alignment_tag index ::
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist row ::
          CauchyFilterConvergenceTasteGate_single_carrier_alignment_pairRows
            (Nat.succ index) rest

def CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow :
    CauchyFilterConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      CauchyFilterConvergenceTasteGate_single_carrier_alignment_pairRows 0
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_fields x)

private def CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt index rest

def CauchyFilterConvergenceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyFilterConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (CauchyFilterConvergenceUp.mk
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 1 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 3 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 5 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 7 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 9 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 11 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 13 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 15 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 17 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 19 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 21 flow))
        (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_eventAt 23 flow)))

private theorem CauchyFilterConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterConvergenceUp,
      CauchyFilterConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B M S D R E W H C P N =>
      change
        some
          (CauchyFilterConvergenceUp.mk
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist F))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist B))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist M))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist S))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist R))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist E))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist W))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist H))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyFilterConvergenceTasteGate_single_carrier_alignment_decodeBHist
              (CauchyFilterConvergenceTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyFilterConvergenceUp.mk F B M S D R E W H C P N)
      rw [CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode F,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode B,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode M,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode S,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyFilterConvergenceUp} :
    CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyFilterConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyFilterConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyFilterConvergenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyFilterConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyFilterConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance CauchyFilterConvergenceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyFilterConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyFilterConvergenceTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyFilterConvergenceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyFilterConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyFilterConvergenceTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact CauchyFilterConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyFilterConvergenceTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyFilterConvergenceUp ∧
      BHistCarrier.toEventFlow
          (CauchyFilterConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [[BMark.b0], [], [BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          [],
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CauchyFilterConvergenceTasteGate_single_carrier_alignment_ChapterTasteGate
  · rfl

end BEDC.Derived.CauchyFilterConvergenceUp
