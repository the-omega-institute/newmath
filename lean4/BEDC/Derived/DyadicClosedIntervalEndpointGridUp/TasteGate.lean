import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicClosedIntervalEndpointGridUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicClosedIntervalEndpointGridUp : Type where
  | mk (I D W R E H C P N : BHist) : DyadicClosedIntervalEndpointGridUp
  deriving DecidableEq

def dyadicClosedIntervalEndpointGridEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicClosedIntervalEndpointGridEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicClosedIntervalEndpointGridEncodeBHist h

def dyadicClosedIntervalEndpointGridDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicClosedIntervalEndpointGridDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicClosedIntervalEndpointGridDecodeBHist tail)

private theorem DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicClosedIntervalEndpointGridDecodeBHist
          (dyadicClosedIntervalEndpointGridEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicClosedIntervalEndpointGridFields :
    DyadicClosedIntervalEndpointGridUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicClosedIntervalEndpointGridUp.mk I D W R E H C P N =>
      [I, D, W, R, E, H, C, P, N]

def dyadicClosedIntervalEndpointGridToEventFlow :
    DyadicClosedIntervalEndpointGridUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicClosedIntervalEndpointGridFields x).map
      dyadicClosedIntervalEndpointGridEncodeBHist

private def dyadicClosedIntervalEndpointGridEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dyadicClosedIntervalEndpointGridEventAtDefault index rest

def dyadicClosedIntervalEndpointGridFromEventFlow
    (ef : EventFlow) : Option DyadicClosedIntervalEndpointGridUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicClosedIntervalEndpointGridUp.mk
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 0 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 1 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 2 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 3 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 4 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 5 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 6 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 7 ef))
      (dyadicClosedIntervalEndpointGridDecodeBHist
        (dyadicClosedIntervalEndpointGridEventAtDefault 8 ef)))

private theorem DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_round_trip
    (x : DyadicClosedIntervalEndpointGridUp) :
    dyadicClosedIntervalEndpointGridFromEventFlow
        (dyadicClosedIntervalEndpointGridToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I D W R E H C P N =>
      change
        some
          (DyadicClosedIntervalEndpointGridUp.mk
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist I))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist D))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist W))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist R))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist E))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist H))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist C))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist P))
            (dyadicClosedIntervalEndpointGridDecodeBHist
              (dyadicClosedIntervalEndpointGridEncodeBHist N))) =
          some (DyadicClosedIntervalEndpointGridUp.mk I D W R E H C P N)
      rw [DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode I,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode D,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode W,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode R,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode E,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode H,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode C,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode P,
        DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode N]

private theorem DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicClosedIntervalEndpointGridUp} :
    dyadicClosedIntervalEndpointGridToEventFlow x =
        dyadicClosedIntervalEndpointGridToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicClosedIntervalEndpointGridFromEventFlow
          (dyadicClosedIntervalEndpointGridToEventFlow x) =
        dyadicClosedIntervalEndpointGridFromEventFlow
          (dyadicClosedIntervalEndpointGridToEventFlow y) :=
    congrArg dyadicClosedIntervalEndpointGridFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicClosedIntervalEndpointGridBHistCarrier :
    BHistCarrier DyadicClosedIntervalEndpointGridUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicClosedIntervalEndpointGridToEventFlow
  fromEventFlow := dyadicClosedIntervalEndpointGridFromEventFlow

instance dyadicClosedIntervalEndpointGridChapterTasteGate :
    ChapterTasteGate DyadicClosedIntervalEndpointGridUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicClosedIntervalEndpointGridFromEventFlow
          (dyadicClosedIntervalEndpointGridToEventFlow x) =
        some x
    exact DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def dyadicClosedIntervalEndpointGridTasteGate :
    ChapterTasteGate DyadicClosedIntervalEndpointGridUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicClosedIntervalEndpointGridChapterTasteGate

theorem DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicClosedIntervalEndpointGridDecodeBHist
          (dyadicClosedIntervalEndpointGridEncodeBHist h) =
        h) ∧
      (∀ x : DyadicClosedIntervalEndpointGridUp,
        dyadicClosedIntervalEndpointGridFromEventFlow
            (dyadicClosedIntervalEndpointGridToEventFlow x) =
          some x) ∧
        Nonempty (BHistCarrier DyadicClosedIntervalEndpointGridUp) ∧
          Nonempty (ChapterTasteGate DyadicClosedIntervalEndpointGridUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_decode,
      DyadicClosedIntervalEndpointGridTasteGate_single_carrier_alignment_round_trip,
      Nonempty.intro dyadicClosedIntervalEndpointGridBHistCarrier,
      Nonempty.intro dyadicClosedIntervalEndpointGridChapterTasteGate⟩

end BEDC.Derived.DyadicClosedIntervalEndpointGridUp
