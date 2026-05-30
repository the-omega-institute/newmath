import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealIntervalHullUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealIntervalHullUp : Type where
  | mk (R S Q D A J L U E T C P N : BHist) : LocatedRealIntervalHullUp
  deriving DecidableEq

def locatedRealIntervalHullEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealIntervalHullEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealIntervalHullEncodeBHist h

def locatedRealIntervalHullDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealIntervalHullDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealIntervalHullDecodeBHist tail)

private theorem LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealIntervalHullFields : LocatedRealIntervalHullUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealIntervalHullUp.mk R S Q D A J L U E T C P N =>
      [R, S, Q, D, A, J, L, U, E, T, C, P, N]

def locatedRealIntervalHullToEventFlow : LocatedRealIntervalHullUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealIntervalHullFields x).map locatedRealIntervalHullEncodeBHist

private def LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt index rest

def locatedRealIntervalHullFromEventFlow : EventFlow → Option LocatedRealIntervalHullUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedRealIntervalHullUp.mk
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 0 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 1 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 2 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 3 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 4 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 5 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 6 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 7 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 8 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 9 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 10 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 11 ef))
        (locatedRealIntervalHullDecodeBHist
          (LocatedRealIntervalHullTasteGate_single_carrier_alignment_eventAt 12 ef)))

private theorem LocatedRealIntervalHullTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealIntervalHullUp,
      locatedRealIntervalHullFromEventFlow (locatedRealIntervalHullToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S Q D A J L U E T C P N =>
      change
        some
          (LocatedRealIntervalHullUp.mk
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist R))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist S))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist Q))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist D))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist A))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist J))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist L))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist U))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist E))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist T))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist C))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist P))
            (locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist N))) =
          some (LocatedRealIntervalHullUp.mk R S Q D A J L U E T C P N)
      rw [LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode R,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode S,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode Q,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode D,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode A,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode J,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode L,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode U,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode E,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode T,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode C,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode P,
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode N]

private theorem LocatedRealIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedRealIntervalHullUp} :
    locatedRealIntervalHullToEventFlow x = locatedRealIntervalHullToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealIntervalHullFromEventFlow (locatedRealIntervalHullToEventFlow x) =
        locatedRealIntervalHullFromEventFlow (locatedRealIntervalHullToEventFlow y) :=
    congrArg locatedRealIntervalHullFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedRealIntervalHullTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealIntervalHullTasteGate_single_carrier_alignment_round_trip y)))

instance locatedRealIntervalHullBHistCarrier : BHistCarrier LocatedRealIntervalHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealIntervalHullToEventFlow
  fromEventFlow := locatedRealIntervalHullFromEventFlow

instance locatedRealIntervalHullChapterTasteGate :
    ChapterTasteGate LocatedRealIntervalHullUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealIntervalHullFromEventFlow (locatedRealIntervalHullToEventFlow x) = some x
    exact LocatedRealIntervalHullTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedRealIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedRealIntervalHullTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealIntervalHullDecodeBHist (locatedRealIntervalHullEncodeBHist h) = h) ∧
      (∀ x : LocatedRealIntervalHullUp,
        locatedRealIntervalHullFromEventFlow (locatedRealIntervalHullToEventFlow x) = some x) ∧
        (∀ x y : LocatedRealIntervalHullUp,
          locatedRealIntervalHullToEventFlow x = locatedRealIntervalHullToEventFlow y →
            x = y) ∧
          locatedRealIntervalHullEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedRealIntervalHullTasteGate_single_carrier_alignment_decode,
      LocatedRealIntervalHullTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedRealIntervalHullTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedRealIntervalHullUp.TasteGate
