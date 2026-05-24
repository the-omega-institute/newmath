import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalFiniteIntersectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalFiniteIntersectionUp : Type where
  | mk (J I W D S R E H C P N : BHist) : ClosedIntervalFiniteIntersectionUp
  deriving DecidableEq

def closedIntervalFiniteIntersectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalFiniteIntersectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalFiniteIntersectionEncodeBHist h

def closedIntervalFiniteIntersectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalFiniteIntersectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalFiniteIntersectionDecodeBHist tail)

private theorem ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalFiniteIntersectionFields :
    ClosedIntervalFiniteIntersectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalFiniteIntersectionUp.mk J I W D S R E H C P N =>
      [J, I, W, D, S, R, E, H, C, P, N]

def closedIntervalFiniteIntersectionToEventFlow :
    ClosedIntervalFiniteIntersectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (closedIntervalFiniteIntersectionFields x).map
      closedIntervalFiniteIntersectionEncodeBHist

def closedIntervalFiniteIntersectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | _index, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ index, _event :: rest =>
      closedIntervalFiniteIntersectionEventAtDefault index rest

def closedIntervalFiniteIntersectionFromEventFlow :
    EventFlow → Option ClosedIntervalFiniteIntersectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ClosedIntervalFiniteIntersectionUp.mk
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 0 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 1 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 2 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 3 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 4 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 5 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 6 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 7 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 8 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 9 ef))
        (closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEventAtDefault 10 ef)))

private theorem ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ClosedIntervalFiniteIntersectionUp,
      closedIntervalFiniteIntersectionFromEventFlow
          (closedIntervalFiniteIntersectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk J I W D S R E H C P N =>
      change
        some
          (ClosedIntervalFiniteIntersectionUp.mk
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist J))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist I))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist W))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist D))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist S))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist R))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist E))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist H))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist C))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist P))
            (closedIntervalFiniteIntersectionDecodeBHist
              (closedIntervalFiniteIntersectionEncodeBHist N))) =
          some (ClosedIntervalFiniteIntersectionUp.mk J I W D S R E H C P N)
      rw [ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode J,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode I,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode W,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode D,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode S,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode R,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode E,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode H,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode C,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode P,
        ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode N]

private theorem ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_injective
    {x y : ClosedIntervalFiniteIntersectionUp} :
    closedIntervalFiniteIntersectionToEventFlow x =
        closedIntervalFiniteIntersectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalFiniteIntersectionFromEventFlow
          (closedIntervalFiniteIntersectionToEventFlow x) =
        closedIntervalFiniteIntersectionFromEventFlow
          (closedIntervalFiniteIntersectionToEventFlow y) :=
    congrArg closedIntervalFiniteIntersectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : ClosedIntervalFiniteIntersectionUp,
      closedIntervalFiniteIntersectionFields x =
          closedIntervalFiniteIntersectionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk J₁ I₁ W₁ D₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk J₂ I₂ W₂ D₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance closedIntervalFiniteIntersectionBHistCarrier :
    BHistCarrier ClosedIntervalFiniteIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalFiniteIntersectionToEventFlow
  fromEventFlow := closedIntervalFiniteIntersectionFromEventFlow

instance closedIntervalFiniteIntersectionChapterTasteGate :
    ChapterTasteGate ClosedIntervalFiniteIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalFiniteIntersectionFromEventFlow
          (closedIntervalFiniteIntersectionToEventFlow x) =
        some x
    exact ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_injective heq)

instance closedIntervalFiniteIntersectionFieldFaithful :
    FieldFaithful ClosedIntervalFiniteIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedIntervalFiniteIntersectionFields
  field_faithful :=
    ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_fields

instance closedIntervalFiniteIntersectionNontrivial :
    Nontrivial ClosedIntervalFiniteIntersectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedIntervalFiniteIntersectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedIntervalFiniteIntersectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClosedIntervalFiniteIntersectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedIntervalFiniteIntersectionChapterTasteGate

theorem ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedIntervalFiniteIntersectionDecodeBHist
          (closedIntervalFiniteIntersectionEncodeBHist h) =
        h) ∧
      (∀ x : ClosedIntervalFiniteIntersectionUp,
        closedIntervalFiniteIntersectionFromEventFlow
            (closedIntervalFiniteIntersectionToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedIntervalFiniteIntersectionUp,
          closedIntervalFiniteIntersectionToEventFlow x =
              closedIntervalFiniteIntersectionToEventFlow y →
            x = y) ∧
          closedIntervalFiniteIntersectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  constructor
  · exact ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ClosedIntervalFiniteIntersectionTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ClosedIntervalFiniteIntersectionUp
