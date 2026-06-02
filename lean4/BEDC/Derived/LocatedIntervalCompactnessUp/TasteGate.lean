import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalCompactnessUp : Type where
  | mk (L E M F W K H C P N : BHist) : LocatedIntervalCompactnessUp
  deriving DecidableEq

def locatedIntervalCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalCompactnessEncodeBHist h

def locatedIntervalCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalCompactnessDecodeBHist tail)

private theorem LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedIntervalCompactnessDecodeBHist
        (locatedIntervalCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalCompactnessFields :
    LocatedIntervalCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalCompactnessUp.mk L E M F W K H C P N =>
      [L, E, M, F, W, K, H, C, P, N]

def locatedIntervalCompactnessToEventFlow :
    LocatedIntervalCompactnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedIntervalCompactnessFields x).map locatedIntervalCompactnessEncodeBHist

private def LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault index rest

def locatedIntervalCompactnessFromEventFlow
    (ef : EventFlow) : Option LocatedIntervalCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalCompactnessUp.mk
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (locatedIntervalCompactnessDecodeBHist
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem LocatedIntervalCompactnessTasteGate_single_carrier_alignment_round_trip
    (x : LocatedIntervalCompactnessUp) :
    locatedIntervalCompactnessFromEventFlow
      (locatedIntervalCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L E M F W K H C P N =>
      change
        some
          (LocatedIntervalCompactnessUp.mk
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist L))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist E))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist M))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist F))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist W))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist K))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist H))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist C))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist P))
            (locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist N))) =
          some (LocatedIntervalCompactnessUp.mk L E M F W K H C P N)
      rw [LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode L,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode E,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode M,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode F,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode W,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode K,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode H,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode C,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode P,
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedIntervalCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalCompactnessUp} :
    locatedIntervalCompactnessToEventFlow x = locatedIntervalCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalCompactnessFromEventFlow (locatedIntervalCompactnessToEventFlow x) =
        locatedIntervalCompactnessFromEventFlow (locatedIntervalCompactnessToEventFlow y) :=
    congrArg locatedIntervalCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_round_trip y)))

instance locatedIntervalCompactnessBHistCarrier :
    BHistCarrier LocatedIntervalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalCompactnessToEventFlow
  fromEventFlow := locatedIntervalCompactnessFromEventFlow

instance locatedIntervalCompactnessChapterTasteGate :
    ChapterTasteGate LocatedIntervalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalCompactnessFromEventFlow
        (locatedIntervalCompactnessToEventFlow x) = some x
    exact LocatedIntervalCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedIntervalCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedIntervalCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedIntervalCompactnessDecodeBHist (locatedIntervalCompactnessEncodeBHist h) = h) ∧
      (∀ x : LocatedIntervalCompactnessUp,
        locatedIntervalCompactnessFromEventFlow
          (locatedIntervalCompactnessToEventFlow x) = some x) ∧
        (∀ x y : LocatedIntervalCompactnessUp,
          locatedIntervalCompactnessToEventFlow x =
            locatedIntervalCompactnessToEventFlow y → x = y) ∧
          locatedIntervalCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedIntervalCompactnessTasteGate_single_carrier_alignment_decode_encode,
      LocatedIntervalCompactnessTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        LocatedIntervalCompactnessTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedIntervalCompactnessUp
