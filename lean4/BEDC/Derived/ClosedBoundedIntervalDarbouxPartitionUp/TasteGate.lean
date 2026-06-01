import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedIntervalDarbouxPartitionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedIntervalDarbouxPartitionUp : Type where
  | mk (I M L U S D J R H C P N : BHist) : ClosedBoundedIntervalDarbouxPartitionUp
  deriving DecidableEq

def closedBoundedIntervalDarbouxPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedIntervalDarbouxPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedIntervalDarbouxPartitionEncodeBHist h

def closedBoundedIntervalDarbouxPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedIntervalDarbouxPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedIntervalDarbouxPartitionDecodeBHist tail)

private theorem ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedBoundedIntervalDarbouxPartitionFields :
    ClosedBoundedIntervalDarbouxPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedIntervalDarbouxPartitionUp.mk I M L U S D J R H C P N =>
      [I, M, L, U, S, D, J, R, H, C, P, N]

def closedBoundedIntervalDarbouxPartitionToEventFlow :
    ClosedBoundedIntervalDarbouxPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (closedBoundedIntervalDarbouxPartitionFields x).map
        closedBoundedIntervalDarbouxPartitionEncodeBHist

private def closedBoundedIntervalDarbouxPartitionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedBoundedIntervalDarbouxPartitionEventAt index rest

def closedBoundedIntervalDarbouxPartitionFromEventFlow
    (ef : EventFlow) : Option ClosedBoundedIntervalDarbouxPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedBoundedIntervalDarbouxPartitionUp.mk
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 0 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 1 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 2 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 3 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 4 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 5 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 6 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 7 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 8 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 9 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 10 ef))
      (closedBoundedIntervalDarbouxPartitionDecodeBHist
        (closedBoundedIntervalDarbouxPartitionEventAt 11 ef)))

private theorem ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedBoundedIntervalDarbouxPartitionUp,
      closedBoundedIntervalDarbouxPartitionFromEventFlow
          (closedBoundedIntervalDarbouxPartitionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I M L U S D J R H C P N =>
      change
        some
            (ClosedBoundedIntervalDarbouxPartitionUp.mk
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist I))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist M))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist L))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist U))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist S))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist D))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist J))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist R))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist H))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist C))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist P))
              (closedBoundedIntervalDarbouxPartitionDecodeBHist
                (closedBoundedIntervalDarbouxPartitionEncodeBHist N))) =
          some (ClosedBoundedIntervalDarbouxPartitionUp.mk I M L U S D J R H C P N)
      rw [ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode I,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode M,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode L,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode U,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode S,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode D,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode J,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode R,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode H,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode C,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode P,
        ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_decode_encode N]

private theorem ClosedBoundedIntervalDarbouxPartitionToEventFlow_injective
    {x y : ClosedBoundedIntervalDarbouxPartitionUp} :
    closedBoundedIntervalDarbouxPartitionToEventFlow x =
        closedBoundedIntervalDarbouxPartitionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedIntervalDarbouxPartitionFromEventFlow
          (closedBoundedIntervalDarbouxPartitionToEventFlow x) =
        closedBoundedIntervalDarbouxPartitionFromEventFlow
          (closedBoundedIntervalDarbouxPartitionToEventFlow y) :=
    congrArg closedBoundedIntervalDarbouxPartitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_round_trip y)))

instance closedBoundedIntervalDarbouxPartitionBHistCarrier :
    BHistCarrier ClosedBoundedIntervalDarbouxPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedIntervalDarbouxPartitionToEventFlow
  fromEventFlow := closedBoundedIntervalDarbouxPartitionFromEventFlow

instance closedBoundedIntervalDarbouxPartitionChapterTasteGate :
    ChapterTasteGate ClosedBoundedIntervalDarbouxPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedBoundedIntervalDarbouxPartitionFromEventFlow
          (closedBoundedIntervalDarbouxPartitionToEventFlow x) =
        some x
    exact ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedBoundedIntervalDarbouxPartitionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ClosedBoundedIntervalDarbouxPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedBoundedIntervalDarbouxPartitionChapterTasteGate

theorem ClosedBoundedIntervalDarbouxPartitionTasteGate_single_carrier_alignment :
    (forall I M L U S D J R H C P N : BHist,
      closedBoundedIntervalDarbouxPartitionFields
          (ClosedBoundedIntervalDarbouxPartitionUp.mk I M L U S D J R H C P N) =
        [I, M, L, U, S, D, J, R, H, C, P, N]) ∧
      closedBoundedIntervalDarbouxPartitionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro I M L U S D J R H C P N
    rfl
  · rfl

end BEDC.Derived.ClosedBoundedIntervalDarbouxPartitionUp.TasteGate
