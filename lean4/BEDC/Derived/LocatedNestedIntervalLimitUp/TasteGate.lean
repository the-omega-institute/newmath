import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedNestedIntervalLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedNestedIntervalLimitUp : Type where
  | mk (I D S R E H C P N : BHist) : LocatedNestedIntervalLimitUp
  deriving DecidableEq

def locatedNestedIntervalLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedNestedIntervalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedNestedIntervalLimitEncodeBHist h

def locatedNestedIntervalLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedNestedIntervalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedNestedIntervalLimitDecodeBHist tail)

private theorem LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedNestedIntervalLimitToEventFlow : LocatedNestedIntervalLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedNestedIntervalLimitUp.mk I D S R E H C P N =>
      [[BMark.b0],
        locatedNestedIntervalLimitEncodeBHist I,
        [BMark.b1, BMark.b0],
        locatedNestedIntervalLimitEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedNestedIntervalLimitEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedNestedIntervalLimitEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedNestedIntervalLimitEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedNestedIntervalLimitEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedNestedIntervalLimitEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedNestedIntervalLimitEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedNestedIntervalLimitEncodeBHist N]

private def locatedNestedIntervalLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedNestedIntervalLimitEventAtDefault index rest

def locatedNestedIntervalLimitFromEventFlow
    (ef : EventFlow) : Option LocatedNestedIntervalLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedNestedIntervalLimitUp.mk
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 1 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 3 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 5 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 7 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 9 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 11 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 13 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 15 ef))
      (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEventAtDefault 17 ef)))

private theorem LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedNestedIntervalLimitUp,
      locatedNestedIntervalLimitFromEventFlow
        (locatedNestedIntervalLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D S R E H C P N =>
      change
        some
          (LocatedNestedIntervalLimitUp.mk
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist I))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist D))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist S))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist R))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist E))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist H))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist C))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist P))
            (locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist N))) =
          some (LocatedNestedIntervalLimitUp.mk I D S R E H C P N)
      rw [LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode I,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode D,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode S,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode R,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode E,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode H,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode C,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode P,
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedNestedIntervalLimitUp} :
    locatedNestedIntervalLimitToEventFlow x = locatedNestedIntervalLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedNestedIntervalLimitFromEventFlow (locatedNestedIntervalLimitToEventFlow x) =
        locatedNestedIntervalLimitFromEventFlow (locatedNestedIntervalLimitToEventFlow y) :=
    congrArg locatedNestedIntervalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_round_trip y)))

instance locatedNestedIntervalLimitBHistCarrier : BHistCarrier LocatedNestedIntervalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedNestedIntervalLimitToEventFlow
  fromEventFlow := locatedNestedIntervalLimitFromEventFlow

instance locatedNestedIntervalLimitChapterTasteGate :
    ChapterTasteGate LocatedNestedIntervalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedNestedIntervalLimitFromEventFlow (locatedNestedIntervalLimitToEventFlow x) =
        some x
    exact LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedNestedIntervalLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedNestedIntervalLimitChapterTasteGate

theorem LocatedNestedIntervalLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedNestedIntervalLimitDecodeBHist (locatedNestedIntervalLimitEncodeBHist h) = h) ∧
      (∀ x : LocatedNestedIntervalLimitUp,
        locatedNestedIntervalLimitFromEventFlow (locatedNestedIntervalLimitToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedNestedIntervalLimitUp,
          locatedNestedIntervalLimitToEventFlow x = locatedNestedIntervalLimitToEventFlow y →
            x = y) ∧
          locatedNestedIntervalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_decode_encode,
      LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        LocatedNestedIntervalLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedNestedIntervalLimitUp
