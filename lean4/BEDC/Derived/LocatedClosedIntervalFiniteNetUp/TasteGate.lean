import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedClosedIntervalFiniteNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedClosedIntervalFiniteNetUp : Type where
  | mk (I M N D W R E H C P L : BHist) : LocatedClosedIntervalFiniteNetUp
  deriving DecidableEq

def locatedClosedIntervalFiniteNetEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedClosedIntervalFiniteNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedClosedIntervalFiniteNetEncodeBHist h

def locatedClosedIntervalFiniteNetDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedClosedIntervalFiniteNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedClosedIntervalFiniteNetDecodeBHist tail)

private theorem locatedClosedIntervalFiniteNet_decode_encode :
    ∀ h : BHist,
      locatedClosedIntervalFiniteNetDecodeBHist
          (locatedClosedIntervalFiniteNetEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedClosedIntervalFiniteNetToEventFlow :
    LocatedClosedIntervalFiniteNetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | LocatedClosedIntervalFiniteNetUp.mk I M N D W R E H C P L =>
      [locatedClosedIntervalFiniteNetEncodeBHist I,
        locatedClosedIntervalFiniteNetEncodeBHist M,
        locatedClosedIntervalFiniteNetEncodeBHist N,
        locatedClosedIntervalFiniteNetEncodeBHist D,
        locatedClosedIntervalFiniteNetEncodeBHist W,
        locatedClosedIntervalFiniteNetEncodeBHist R,
        locatedClosedIntervalFiniteNetEncodeBHist E,
        locatedClosedIntervalFiniteNetEncodeBHist H,
        locatedClosedIntervalFiniteNetEncodeBHist C,
        locatedClosedIntervalFiniteNetEncodeBHist P,
        locatedClosedIntervalFiniteNetEncodeBHist L]

private def locatedClosedIntervalFiniteNetEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedClosedIntervalFiniteNetEventAt index rest

def locatedClosedIntervalFiniteNetFromEventFlow :
    EventFlow → Option LocatedClosedIntervalFiniteNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedClosedIntervalFiniteNetUp.mk
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 0 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 1 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 2 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 3 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 4 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 5 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 6 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 7 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 8 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 9 ef))
        (locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEventAt 10 ef)))

private theorem locatedClosedIntervalFiniteNet_round_trip :
    ∀ x : LocatedClosedIntervalFiniteNetUp,
      locatedClosedIntervalFiniteNetFromEventFlow
          (locatedClosedIntervalFiniteNetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M N D W R E H C P L =>
      change
        some
          (LocatedClosedIntervalFiniteNetUp.mk
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist I))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist M))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist N))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist D))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist W))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist R))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist E))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist H))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist C))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist P))
            (locatedClosedIntervalFiniteNetDecodeBHist
              (locatedClosedIntervalFiniteNetEncodeBHist L))) =
          some (LocatedClosedIntervalFiniteNetUp.mk I M N D W R E H C P L)
      rw [locatedClosedIntervalFiniteNet_decode_encode I,
        locatedClosedIntervalFiniteNet_decode_encode M,
        locatedClosedIntervalFiniteNet_decode_encode N,
        locatedClosedIntervalFiniteNet_decode_encode D,
        locatedClosedIntervalFiniteNet_decode_encode W,
        locatedClosedIntervalFiniteNet_decode_encode R,
        locatedClosedIntervalFiniteNet_decode_encode E,
        locatedClosedIntervalFiniteNet_decode_encode H,
        locatedClosedIntervalFiniteNet_decode_encode C,
        locatedClosedIntervalFiniteNet_decode_encode P,
        locatedClosedIntervalFiniteNet_decode_encode L]

private theorem LocatedClosedIntervalFiniteNetToEventFlow_injective
    {x y : LocatedClosedIntervalFiniteNetUp} :
    locatedClosedIntervalFiniteNetToEventFlow x =
        locatedClosedIntervalFiniteNetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          locatedClosedIntervalFiniteNetFromEventFlow
            (locatedClosedIntervalFiniteNetToEventFlow x) :=
        (locatedClosedIntervalFiniteNet_round_trip x).symm
      _ =
          locatedClosedIntervalFiniteNetFromEventFlow
            (locatedClosedIntervalFiniteNetToEventFlow y) :=
        congrArg locatedClosedIntervalFiniteNetFromEventFlow hxy
      _ = some y := locatedClosedIntervalFiniteNet_round_trip y
  exact Option.some.inj hsome

instance locatedClosedIntervalFiniteNetBHistCarrier :
    BHistCarrier LocatedClosedIntervalFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedClosedIntervalFiniteNetToEventFlow
  fromEventFlow := locatedClosedIntervalFiniteNetFromEventFlow

instance locatedClosedIntervalFiniteNetChapterTasteGate :
    ChapterTasteGate LocatedClosedIntervalFiniteNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedClosedIntervalFiniteNetFromEventFlow
          (locatedClosedIntervalFiniteNetToEventFlow x) =
        some x
    exact locatedClosedIntervalFiniteNet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedClosedIntervalFiniteNetToEventFlow_injective heq)

theorem LocatedClosedIntervalFiniteNetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedClosedIntervalFiniteNetDecodeBHist (locatedClosedIntervalFiniteNetEncodeBHist h) =
        h) ∧
      (∀ x : LocatedClosedIntervalFiniteNetUp,
        locatedClosedIntervalFiniteNetFromEventFlow
            (locatedClosedIntervalFiniteNetToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedClosedIntervalFiniteNetUp,
          locatedClosedIntervalFiniteNetToEventFlow x =
              locatedClosedIntervalFiniteNetToEventFlow y →
            x = y) ∧
          locatedClosedIntervalFiniteNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact locatedClosedIntervalFiniteNet_decode_encode
  · constructor
    · exact locatedClosedIntervalFiniteNet_round_trip
    · constructor
      · intro x y heq
        exact LocatedClosedIntervalFiniteNetToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedClosedIntervalFiniteNetUp
