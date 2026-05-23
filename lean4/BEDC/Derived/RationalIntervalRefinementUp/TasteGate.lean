import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalIntervalRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalIntervalRefinementUp : Type where
  | mk (I J E W K H C P N : BHist) : RationalIntervalRefinementUp
  deriving DecidableEq

def rationalIntervalRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalIntervalRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalIntervalRefinementEncodeBHist h

def rationalIntervalRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalIntervalRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalIntervalRefinementDecodeBHist tail)

private theorem RationalIntervalRefinementTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalIntervalRefinementFields : RationalIntervalRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalIntervalRefinementUp.mk I J E W K H C P N => [I, J, E, W, K, H, C, P, N]

def rationalIntervalRefinementToEventFlow : RationalIntervalRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map rationalIntervalRefinementEncodeBHist
        (rationalIntervalRefinementFields x)

private def rationalIntervalRefinementEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalIntervalRefinementEventAt index rest

def rationalIntervalRefinementFromEventFlow :
    EventFlow → Option RationalIntervalRefinementUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RationalIntervalRefinementUp.mk
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 0 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 1 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 2 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 3 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 4 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 5 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 6 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 7 ef))
          (rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEventAt 8 ef)))

private theorem RationalIntervalRefinementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RationalIntervalRefinementUp,
      rationalIntervalRefinementFromEventFlow (rationalIntervalRefinementToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J E W K H C P N =>
      change
        some
          (RationalIntervalRefinementUp.mk
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist I))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist J))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist E))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist W))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist K))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist H))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist C))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist P))
            (rationalIntervalRefinementDecodeBHist
              (rationalIntervalRefinementEncodeBHist N))) =
          some (RationalIntervalRefinementUp.mk I J E W K H C P N)
      rw [RationalIntervalRefinementTasteGate_single_carrier_alignment_decode I,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode J,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode E,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode W,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode K,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode H,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode C,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode P,
        RationalIntervalRefinementTasteGate_single_carrier_alignment_decode N]

private theorem RationalIntervalRefinementTasteGate_single_carrier_alignment_injective
    {x y : RationalIntervalRefinementUp} :
    rationalIntervalRefinementToEventFlow x = rationalIntervalRefinementToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalIntervalRefinementFromEventFlow (rationalIntervalRefinementToEventFlow x) =
        rationalIntervalRefinementFromEventFlow (rationalIntervalRefinementToEventFlow y) :=
    congrArg rationalIntervalRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RationalIntervalRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalIntervalRefinementTasteGate_single_carrier_alignment_round_trip y)))

instance rationalIntervalRefinementBHistCarrier :
    BHistCarrier RationalIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalIntervalRefinementToEventFlow
  fromEventFlow := rationalIntervalRefinementFromEventFlow

instance rationalIntervalRefinementChapterTasteGate :
    ChapterTasteGate RationalIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalIntervalRefinementFromEventFlow (rationalIntervalRefinementToEventFlow x) =
        some x
    exact RationalIntervalRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RationalIntervalRefinementTasteGate_single_carrier_alignment_injective heq)

theorem RationalIntervalRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      rationalIntervalRefinementDecodeBHist (rationalIntervalRefinementEncodeBHist h) =
        h) ∧
      (∀ x : RationalIntervalRefinementUp,
        rationalIntervalRefinementFromEventFlow (rationalIntervalRefinementToEventFlow x) =
          some x) ∧
        (∀ x y : RationalIntervalRefinementUp,
          rationalIntervalRefinementToEventFlow x =
              rationalIntervalRefinementToEventFlow y →
            x = y) ∧
          rationalIntervalRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RationalIntervalRefinementTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RationalIntervalRefinementTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RationalIntervalRefinementTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.RationalIntervalRefinementUp
