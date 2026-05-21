import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneSequenceConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneSequenceConvergenceUp : Type where
  | mk (S W Q R B M T H C P N : BHist) : MonotoneSequenceConvergenceUp
  deriving DecidableEq

def monotoneSequenceConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneSequenceConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneSequenceConvergenceEncodeBHist h

def monotoneSequenceConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneSequenceConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneSequenceConvergenceDecodeBHist tail)

private theorem MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      monotoneSequenceConvergenceDecodeBHist (monotoneSequenceConvergenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneSequenceConvergenceFields : MonotoneSequenceConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneSequenceConvergenceUp.mk S W Q R B M T H C P N =>
      [S, W, Q, R, B, M, T, H, C, P, N]

def monotoneSequenceConvergenceToEventFlow : MonotoneSequenceConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map monotoneSequenceConvergenceEncodeBHist
        (monotoneSequenceConvergenceFields x)

private def monotoneSequenceConvergenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneSequenceConvergenceEventAt index rest

def monotoneSequenceConvergenceFromEventFlow :
    EventFlow → Option MonotoneSequenceConvergenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (MonotoneSequenceConvergenceUp.mk
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 0 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 1 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 2 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 3 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 4 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 5 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 6 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 7 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 8 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 9 ef))
          (monotoneSequenceConvergenceDecodeBHist
            (monotoneSequenceConvergenceEventAt 10 ef)))

private theorem MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MonotoneSequenceConvergenceUp,
      monotoneSequenceConvergenceFromEventFlow
          (monotoneSequenceConvergenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W Q R B M T H C P N =>
      change
        some
          (MonotoneSequenceConvergenceUp.mk
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist S))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist W))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist Q))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist R))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist B))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist M))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist T))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist H))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist C))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist P))
            (monotoneSequenceConvergenceDecodeBHist
              (monotoneSequenceConvergenceEncodeBHist N))) =
          some (MonotoneSequenceConvergenceUp.mk S W Q R B M T H C P N)
      rw [MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode S,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode W,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode Q,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode R,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode B,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode M,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode T,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode H,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode C,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode P,
        MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode N]

private theorem MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_injective
    {x y : MonotoneSequenceConvergenceUp} :
    monotoneSequenceConvergenceToEventFlow x = monotoneSequenceConvergenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneSequenceConvergenceFromEventFlow (monotoneSequenceConvergenceToEventFlow x) =
        monotoneSequenceConvergenceFromEventFlow
          (monotoneSequenceConvergenceToEventFlow y) :=
    congrArg monotoneSequenceConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance monotoneSequenceConvergenceBHistCarrier :
    BHistCarrier MonotoneSequenceConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneSequenceConvergenceToEventFlow
  fromEventFlow := monotoneSequenceConvergenceFromEventFlow

instance monotoneSequenceConvergenceChapterTasteGate :
    ChapterTasteGate MonotoneSequenceConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      monotoneSequenceConvergenceFromEventFlow
          (monotoneSequenceConvergenceToEventFlow x) =
        some x
    exact MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_injective heq)

theorem MonotoneSequenceConvergenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      monotoneSequenceConvergenceDecodeBHist (monotoneSequenceConvergenceEncodeBHist h) =
        h) ∧
      (∀ x : MonotoneSequenceConvergenceUp,
        monotoneSequenceConvergenceFromEventFlow
            (monotoneSequenceConvergenceToEventFlow x) =
          some x) ∧
        (∀ x y : MonotoneSequenceConvergenceUp,
          monotoneSequenceConvergenceToEventFlow x =
              monotoneSequenceConvergenceToEventFlow y →
            x = y) ∧
          monotoneSequenceConvergenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MonotoneSequenceConvergenceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.MonotoneSequenceConvergenceUp
