import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalBisectionTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalBisectionTreeUp : Type where
  | mk (I D B Q W S R H C P N : BHist) : IntervalBisectionTreeUp
  deriving DecidableEq

def intervalBisectionTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalBisectionTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalBisectionTreeEncodeBHist h

def intervalBisectionTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalBisectionTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalBisectionTreeDecodeBHist tail)

private theorem IntervalBisectionTreeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalBisectionTreeFields : IntervalBisectionTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalBisectionTreeUp.mk I D B Q W S R H C P N => [I, D, B, Q, W, S, R, H, C, P, N]

def intervalBisectionTreeToEventFlow : IntervalBisectionTreeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (intervalBisectionTreeFields x).map intervalBisectionTreeEncodeBHist

def intervalBisectionTreeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => intervalBisectionTreeEventAtDefault index rest

def intervalBisectionTreeFromEventFlow :
    EventFlow → Option IntervalBisectionTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (IntervalBisectionTreeUp.mk
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 0 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 1 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 2 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 3 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 4 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 5 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 6 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 7 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 8 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 9 ef))
        (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEventAtDefault 10 ef)))

private theorem IntervalBisectionTreeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntervalBisectionTreeUp,
      intervalBisectionTreeFromEventFlow (intervalBisectionTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D B Q W S R H C P N =>
      change
        some
          (IntervalBisectionTreeUp.mk
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist I))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist D))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist B))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist Q))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist W))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist S))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist R))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist H))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist C))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist P))
            (intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist N))) =
          some (IntervalBisectionTreeUp.mk I D B Q W S R H C P N)
      rw [IntervalBisectionTreeTasteGate_single_carrier_alignment_decode I,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode D,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode B,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode Q,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode W,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode S,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode R,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode H,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode C,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode P,
        IntervalBisectionTreeTasteGate_single_carrier_alignment_decode N]

private theorem IntervalBisectionTreeTasteGate_single_carrier_alignment_injective
    {x y : IntervalBisectionTreeUp} :
    intervalBisectionTreeToEventFlow x =
      intervalBisectionTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalBisectionTreeFromEventFlow
          (intervalBisectionTreeToEventFlow x) =
        intervalBisectionTreeFromEventFlow
          (intervalBisectionTreeToEventFlow y) :=
    congrArg intervalBisectionTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IntervalBisectionTreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (IntervalBisectionTreeTasteGate_single_carrier_alignment_round_trip y)))

instance intervalBisectionTreeBHistCarrier :
    BHistCarrier IntervalBisectionTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalBisectionTreeToEventFlow
  fromEventFlow := intervalBisectionTreeFromEventFlow

instance intervalBisectionTreeChapterTasteGate :
    ChapterTasteGate IntervalBisectionTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intervalBisectionTreeFromEventFlow
        (intervalBisectionTreeToEventFlow x) = some x
    exact IntervalBisectionTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalBisectionTreeTasteGate_single_carrier_alignment_injective heq)

theorem IntervalBisectionTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      intervalBisectionTreeDecodeBHist (intervalBisectionTreeEncodeBHist h) = h) ∧
      (∀ x : IntervalBisectionTreeUp,
        intervalBisectionTreeFromEventFlow
          (intervalBisectionTreeToEventFlow x) = some x) ∧
      (∀ x y : IntervalBisectionTreeUp,
        intervalBisectionTreeToEventFlow x =
          intervalBisectionTreeToEventFlow y → x = y) ∧
      intervalBisectionTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact IntervalBisectionTreeTasteGate_single_carrier_alignment_decode
  constructor
  · exact IntervalBisectionTreeTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact IntervalBisectionTreeTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.IntervalBisectionTreeUp
