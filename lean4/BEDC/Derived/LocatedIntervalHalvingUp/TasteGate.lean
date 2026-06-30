import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalHalvingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalHalvingUp : Type where
  | mk (I M L R S D Q E T C P N : BHist) : LocatedIntervalHalvingUp
  deriving DecidableEq

def locatedIntervalHalvingEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalHalvingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalHalvingEncodeBHist h

def locatedIntervalHalvingDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalHalvingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalHalvingDecodeBHist tail)

private theorem LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalHalvingToEventFlow : LocatedIntervalHalvingUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalHalvingUp.mk I M L R S D Q E T C P N =>
      [locatedIntervalHalvingEncodeBHist I,
        locatedIntervalHalvingEncodeBHist M,
        locatedIntervalHalvingEncodeBHist L,
        locatedIntervalHalvingEncodeBHist R,
        locatedIntervalHalvingEncodeBHist S,
        locatedIntervalHalvingEncodeBHist D,
        locatedIntervalHalvingEncodeBHist Q,
        locatedIntervalHalvingEncodeBHist E,
        locatedIntervalHalvingEncodeBHist T,
        locatedIntervalHalvingEncodeBHist C,
        locatedIntervalHalvingEncodeBHist P,
        locatedIntervalHalvingEncodeBHist N]

private def locatedIntervalHalvingEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalHalvingEventAt index rest

def locatedIntervalHalvingDecodeFields (ef : EventFlow) : LocatedIntervalHalvingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LocatedIntervalHalvingUp.mk
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 0 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 1 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 2 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 3 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 4 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 5 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 6 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 7 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 8 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 9 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 10 ef))
    (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEventAt 11 ef))

def locatedIntervalHalvingFromEventFlow :
    EventFlow -> Option LocatedIntervalHalvingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef => some (locatedIntervalHalvingDecodeFields ef)

private theorem LocatedIntervalHalvingTasteGate_single_carrier_alignment_round_trip
    (x : LocatedIntervalHalvingUp) :
    locatedIntervalHalvingFromEventFlow (locatedIntervalHalvingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I M L R S D Q E T C P N =>
      change
        some
            (LocatedIntervalHalvingUp.mk
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist I))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist M))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist L))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist R))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist S))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist D))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist Q))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist E))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist T))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist C))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist P))
              (locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist N))) =
          some (LocatedIntervalHalvingUp.mk I M L R S D Q E T C P N)
      rw [LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode I,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode M,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode L,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode R,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode S,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode D,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode E,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode T,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode C,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode P,
        LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedIntervalHalvingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalHalvingUp} :
    locatedIntervalHalvingToEventFlow x = locatedIntervalHalvingToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalHalvingFromEventFlow (locatedIntervalHalvingToEventFlow x) =
        locatedIntervalHalvingFromEventFlow (locatedIntervalHalvingToEventFlow y) :=
    congrArg locatedIntervalHalvingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedIntervalHalvingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalHalvingTasteGate_single_carrier_alignment_round_trip y)))

instance locatedIntervalHalvingBHistCarrier : BHistCarrier LocatedIntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalHalvingToEventFlow
  fromEventFlow := locatedIntervalHalvingFromEventFlow

instance locatedIntervalHalvingChapterTasteGate :
    ChapterTasteGate LocatedIntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalHalvingFromEventFlow (locatedIntervalHalvingToEventFlow x) = some x
    exact LocatedIntervalHalvingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedIntervalHalvingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedIntervalHalvingTasteGate_single_carrier_alignment :
    (forall h : BHist,
      locatedIntervalHalvingDecodeBHist (locatedIntervalHalvingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedIntervalHalvingUp) ∧
        Nonempty (ChapterTasteGate LocatedIntervalHalvingUp) ∧
          locatedIntervalHalvingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedIntervalHalvingTasteGate_single_carrier_alignment_decode_encode,
      ⟨locatedIntervalHalvingBHistCarrier⟩,
      ⟨locatedIntervalHalvingChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedIntervalHalvingUp
