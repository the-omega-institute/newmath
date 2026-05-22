import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealNestedIntervalsUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealNestedIntervalsUp : Type where
  | mk (I B M D J S R E H C P N : BHist) : LocatedRealNestedIntervalsUp
  deriving DecidableEq

def locatedRealNestedIntervalsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealNestedIntervalsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealNestedIntervalsEncodeBHist h

def locatedRealNestedIntervalsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealNestedIntervalsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealNestedIntervalsDecodeBHist tail)

private theorem locatedRealNestedIntervals_decode_encode :
    ∀ h : BHist,
      locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealNestedIntervalsFields : LocatedRealNestedIntervalsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealNestedIntervalsUp.mk I B M D J S R E H C P N =>
      [I, B, M, D, J, S, R, E, H, C, P, N]

def locatedRealNestedIntervalsToEventFlow : LocatedRealNestedIntervalsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealNestedIntervalsFields x).map locatedRealNestedIntervalsEncodeBHist

private def locatedRealNestedIntervalsEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealNestedIntervalsEventAtDefault index rest

def locatedRealNestedIntervalsFromEventFlow (ef : EventFlow) :
    Option LocatedRealNestedIntervalsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealNestedIntervalsUp.mk
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 0 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 1 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 2 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 3 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 4 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 5 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 6 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 7 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 8 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 9 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 10 ef))
      (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEventAtDefault 11 ef)))

private theorem locatedRealNestedIntervals_round_trip :
    ∀ x : LocatedRealNestedIntervalsUp,
      locatedRealNestedIntervalsFromEventFlow (locatedRealNestedIntervalsToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B M D J S R E H C P N =>
      change
        some
          (LocatedRealNestedIntervalsUp.mk
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist I))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist B))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist M))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist D))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist J))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist S))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist R))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist E))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist H))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist C))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist P))
            (locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist N))) =
          some (LocatedRealNestedIntervalsUp.mk I B M D J S R E H C P N)
      rw [locatedRealNestedIntervals_decode_encode I,
        locatedRealNestedIntervals_decode_encode B,
        locatedRealNestedIntervals_decode_encode M,
        locatedRealNestedIntervals_decode_encode D,
        locatedRealNestedIntervals_decode_encode J,
        locatedRealNestedIntervals_decode_encode S,
        locatedRealNestedIntervals_decode_encode R,
        locatedRealNestedIntervals_decode_encode E,
        locatedRealNestedIntervals_decode_encode H,
        locatedRealNestedIntervals_decode_encode C,
        locatedRealNestedIntervals_decode_encode P,
        locatedRealNestedIntervals_decode_encode N]

private theorem locatedRealNestedIntervalsToEventFlow_injective
    {x y : LocatedRealNestedIntervalsUp} :
    locatedRealNestedIntervalsToEventFlow x = locatedRealNestedIntervalsToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealNestedIntervalsFromEventFlow (locatedRealNestedIntervalsToEventFlow x) =
        locatedRealNestedIntervalsFromEventFlow (locatedRealNestedIntervalsToEventFlow y) :=
    congrArg locatedRealNestedIntervalsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealNestedIntervals_round_trip x).symm
      (Eq.trans hread (locatedRealNestedIntervals_round_trip y)))

private theorem locatedRealNestedIntervals_field_faithful :
    ∀ x y : LocatedRealNestedIntervalsUp,
      locatedRealNestedIntervalsFields x = locatedRealNestedIntervalsFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 B1 M1 D1 J1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 B2 M2 D2 J2 S2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance locatedRealNestedIntervalsBHistCarrier :
    BHistCarrier LocatedRealNestedIntervalsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealNestedIntervalsToEventFlow
  fromEventFlow := locatedRealNestedIntervalsFromEventFlow

instance locatedRealNestedIntervalsChapterTasteGate :
    ChapterTasteGate LocatedRealNestedIntervalsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealNestedIntervalsFromEventFlow (locatedRealNestedIntervalsToEventFlow x) =
        some x
    exact locatedRealNestedIntervals_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealNestedIntervalsToEventFlow_injective heq)

instance locatedRealNestedIntervalsFieldFaithful :
    FieldFaithful LocatedRealNestedIntervalsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealNestedIntervalsFields
  field_faithful := locatedRealNestedIntervals_field_faithful

instance locatedRealNestedIntervalsNontrivial :
    Nontrivial LocatedRealNestedIntervalsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealNestedIntervalsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedRealNestedIntervalsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealNestedIntervalsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealNestedIntervalsChapterTasteGate

theorem LocatedRealNestedIntervalsTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedRealNestedIntervalsUp) ∧
      Nonempty (FieldFaithful LocatedRealNestedIntervalsUp) ∧
      Nonempty (Nontrivial LocatedRealNestedIntervalsUp) ∧
      (∀ h : BHist,
        locatedRealNestedIntervalsDecodeBHist (locatedRealNestedIntervalsEncodeBHist h) = h) ∧
      (∀ x : LocatedRealNestedIntervalsUp,
        locatedRealNestedIntervalsFromEventFlow
          (locatedRealNestedIntervalsToEventFlow x) = some x) ∧
      locatedRealNestedIntervalsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨Nonempty.intro locatedRealNestedIntervalsChapterTasteGate,
      Nonempty.intro locatedRealNestedIntervalsFieldFaithful,
      Nonempty.intro locatedRealNestedIntervalsNontrivial,
      locatedRealNestedIntervals_decode_encode,
      locatedRealNestedIntervals_round_trip,
      rfl⟩

end BEDC.Derived.LocatedRealNestedIntervalsUp.TasteGate
