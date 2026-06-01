import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalNestingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalNestingUp : Type where
  | mk (E I S W R Q H C P N : BHist) : ClosedIntervalNestingUp
  deriving DecidableEq

def closedIntervalNestingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalNestingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalNestingEncodeBHist h

def closedIntervalNestingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalNestingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalNestingDecodeBHist tail)

private theorem ClosedIntervalNestingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedIntervalNestingFields : ClosedIntervalNestingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalNestingUp.mk E I S W R Q H C P N => [E, I, S, W, R, Q, H, C, P, N]

def closedIntervalNestingToEventFlow : ClosedIntervalNestingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (closedIntervalNestingFields x).map closedIntervalNestingEncodeBHist

private def closedIntervalNestingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => closedIntervalNestingEventAt index rest

def closedIntervalNestingFromEventFlow (ef : EventFlow) : Option ClosedIntervalNestingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedIntervalNestingUp.mk
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 0 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 1 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 2 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 3 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 4 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 5 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 6 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 7 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 8 ef))
      (closedIntervalNestingDecodeBHist (closedIntervalNestingEventAt 9 ef)))

private theorem ClosedIntervalNestingTasteGate_single_carrier_alignment_round_trip
    (x : ClosedIntervalNestingUp) :
    closedIntervalNestingFromEventFlow (closedIntervalNestingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E I S W R Q H C P N =>
      change
        some
          (ClosedIntervalNestingUp.mk
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist E))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist I))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist S))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist W))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist R))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist Q))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist H))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist C))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist P))
            (closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist N))) =
          some (ClosedIntervalNestingUp.mk E I S W R Q H C P N)
      rw [ClosedIntervalNestingTasteGate_single_carrier_alignment_decode E,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode I,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode S,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode W,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode R,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode Q,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode H,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode C,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode P,
        ClosedIntervalNestingTasteGate_single_carrier_alignment_decode N]

private theorem ClosedIntervalNestingTasteGate_single_carrier_alignment_injective
    {x y : ClosedIntervalNestingUp} :
    closedIntervalNestingToEventFlow x = closedIntervalNestingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalNestingFromEventFlow (closedIntervalNestingToEventFlow x) =
        closedIntervalNestingFromEventFlow (closedIntervalNestingToEventFlow y) :=
    congrArg closedIntervalNestingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ClosedIntervalNestingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ClosedIntervalNestingTasteGate_single_carrier_alignment_round_trip y)))

private theorem ClosedIntervalNestingTasteGate_single_carrier_alignment_fields :
    ∀ x y : ClosedIntervalNestingUp,
      closedIntervalNestingFields x = closedIntervalNestingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ I₁ S₁ W₁ R₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ I₂ S₂ W₂ R₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance closedIntervalNestingBHistCarrier : BHistCarrier ClosedIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalNestingToEventFlow
  fromEventFlow := closedIntervalNestingFromEventFlow

instance closedIntervalNestingChapterTasteGate :
    ChapterTasteGate ClosedIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change closedIntervalNestingFromEventFlow (closedIntervalNestingToEventFlow x) = some x
    exact ClosedIntervalNestingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ClosedIntervalNestingTasteGate_single_carrier_alignment_injective heq)

instance closedIntervalNestingFieldFaithful : FieldFaithful ClosedIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedIntervalNestingFields
  field_faithful := ClosedIntervalNestingTasteGate_single_carrier_alignment_fields

instance closedIntervalNestingNontrivial : Nontrivial ClosedIntervalNestingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedIntervalNestingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClosedIntervalNestingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def closedIntervalNestingTasteGate : ChapterTasteGate ClosedIntervalNestingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  closedIntervalNestingChapterTasteGate

theorem ClosedIntervalNestingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClosedIntervalNestingUp) ∧
      Nonempty (FieldFaithful ClosedIntervalNestingUp) ∧
        Nonempty (Nontrivial ClosedIntervalNestingUp) ∧
          (∀ h : BHist,
            closedIntervalNestingDecodeBHist (closedIntervalNestingEncodeBHist h) = h) ∧
            (∀ x : ClosedIntervalNestingUp,
              closedIntervalNestingFromEventFlow (closedIntervalNestingToEventFlow x) =
                some x) ∧
              (∀ x y : ClosedIntervalNestingUp,
                closedIntervalNestingToEventFlow x = closedIntervalNestingToEventFlow y ->
                  x = y) ∧
                closedIntervalNestingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨closedIntervalNestingChapterTasteGate⟩,
      ⟨closedIntervalNestingFieldFaithful⟩,
      ⟨closedIntervalNestingNontrivial⟩,
      ClosedIntervalNestingTasteGate_single_carrier_alignment_decode,
      ClosedIntervalNestingTasteGate_single_carrier_alignment_round_trip,
      fun x y => ClosedIntervalNestingTasteGate_single_carrier_alignment_injective,
      rfl⟩

end BEDC.Derived.ClosedIntervalNestingUp.TasteGate
