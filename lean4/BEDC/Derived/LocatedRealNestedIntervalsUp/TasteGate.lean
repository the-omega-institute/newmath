import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealNestedIntervalsUp

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

private theorem LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode :
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

def locatedRealNestedIntervalsFromEventFlow :
    EventFlow → Option LocatedRealNestedIntervalsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LocatedRealNestedIntervalsUp.mk
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 0 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 1 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 2 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 3 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 4 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 5 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 6 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 7 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 8 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 9 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 10 ef))
        (locatedRealNestedIntervalsDecodeBHist
          (locatedRealNestedIntervalsEventAtDefault 11 ef)))

private theorem LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealNestedIntervalsUp,
      locatedRealNestedIntervalsFromEventFlow (locatedRealNestedIntervalsToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
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
      rw [LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode I,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode B,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode M,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode D,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode J,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode S,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode R,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode E,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode H,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode C,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode P,
        LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_toEventFlow_injective
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
    (Eq.trans (LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedRealNestedIntervalsUp,
      locatedRealNestedIntervalsFields x = locatedRealNestedIntervalsFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ B₁ M₁ D₁ J₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ B₂ M₂ D₂ J₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
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
    exact LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedRealNestedIntervalsFieldFaithful :
    FieldFaithful LocatedRealNestedIntervalsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealNestedIntervalsFields
  field_faithful :=
    LocatedRealNestedIntervalsTasteGate_single_carrier_alignment_fields_faithful

instance locatedRealNestedIntervalsNontrivial : Nontrivial LocatedRealNestedIntervalsUp where
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
    ChapterTasteGate LocatedRealNestedIntervalsUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact locatedRealNestedIntervalsChapterTasteGate

end BEDC.Derived.LocatedRealNestedIntervalsUp
