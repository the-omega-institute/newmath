import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLocatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLocatorUp : Type where
  | mk (X Q S R D A H C P N : BHist) : RealLocatorUp
  deriving DecidableEq

def realLocatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLocatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLocatorEncodeBHist h

def realLocatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLocatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLocatorDecodeBHist tail)

private theorem RealLocatorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realLocatorDecodeBHist (realLocatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLocatorToEventFlow : RealLocatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealLocatorUp.mk X Q S R D A H C P N =>
      [realLocatorEncodeBHist X,
        realLocatorEncodeBHist Q,
        realLocatorEncodeBHist S,
        realLocatorEncodeBHist R,
        realLocatorEncodeBHist D,
        realLocatorEncodeBHist A,
        realLocatorEncodeBHist H,
        realLocatorEncodeBHist C,
        realLocatorEncodeBHist P,
        realLocatorEncodeBHist N]

private def realLocatorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realLocatorEventAt index rest

def realLocatorFromEventFlow (ef : EventFlow) : Option RealLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealLocatorUp.mk
      (realLocatorDecodeBHist (realLocatorEventAt 0 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 1 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 2 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 3 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 4 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 5 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 6 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 7 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 8 ef))
      (realLocatorDecodeBHist (realLocatorEventAt 9 ef)))

private theorem RealLocatorTasteGate_single_carrier_alignment_round_trip
    (x : RealLocatorUp) :
    realLocatorFromEventFlow (realLocatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Q S R D A H C P N =>
      change
        some
          (RealLocatorUp.mk
            (realLocatorDecodeBHist (realLocatorEncodeBHist X))
            (realLocatorDecodeBHist (realLocatorEncodeBHist Q))
            (realLocatorDecodeBHist (realLocatorEncodeBHist S))
            (realLocatorDecodeBHist (realLocatorEncodeBHist R))
            (realLocatorDecodeBHist (realLocatorEncodeBHist D))
            (realLocatorDecodeBHist (realLocatorEncodeBHist A))
            (realLocatorDecodeBHist (realLocatorEncodeBHist H))
            (realLocatorDecodeBHist (realLocatorEncodeBHist C))
            (realLocatorDecodeBHist (realLocatorEncodeBHist P))
            (realLocatorDecodeBHist (realLocatorEncodeBHist N))) =
          some (RealLocatorUp.mk X Q S R D A H C P N)
      rw [RealLocatorTasteGate_single_carrier_alignment_decode X,
        RealLocatorTasteGate_single_carrier_alignment_decode Q,
        RealLocatorTasteGate_single_carrier_alignment_decode S,
        RealLocatorTasteGate_single_carrier_alignment_decode R,
        RealLocatorTasteGate_single_carrier_alignment_decode D,
        RealLocatorTasteGate_single_carrier_alignment_decode A,
        RealLocatorTasteGate_single_carrier_alignment_decode H,
        RealLocatorTasteGate_single_carrier_alignment_decode C,
        RealLocatorTasteGate_single_carrier_alignment_decode P,
        RealLocatorTasteGate_single_carrier_alignment_decode N]

private theorem RealLocatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealLocatorUp} :
    realLocatorToEventFlow x = realLocatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLocatorFromEventFlow (realLocatorToEventFlow x) =
        realLocatorFromEventFlow (realLocatorToEventFlow y) :=
    congrArg realLocatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealLocatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealLocatorTasteGate_single_carrier_alignment_round_trip y)))

instance realLocatorBHistCarrier : BHistCarrier RealLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLocatorToEventFlow
  fromEventFlow := realLocatorFromEventFlow

instance realLocatorChapterTasteGate : ChapterTasteGate RealLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLocatorFromEventFlow (realLocatorToEventFlow x) = some x
    exact RealLocatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealLocatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def RealLocatorTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RealLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realLocatorChapterTasteGate

theorem RealLocatorTasteGate_single_carrier_alignment :
    (∀ h : BHist, realLocatorDecodeBHist (realLocatorEncodeBHist h) = h) ∧
      (∀ x : RealLocatorUp,
        realLocatorFromEventFlow (realLocatorToEventFlow x) = some x) ∧
        (∀ x y : RealLocatorUp,
          realLocatorToEventFlow x = realLocatorToEventFlow y → x = y) ∧
          realLocatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealLocatorTasteGate_single_carrier_alignment_decode,
      RealLocatorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RealLocatorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealLocatorUp
