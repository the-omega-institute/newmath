import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyOscillationCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyOscillationCriterionUp : Type where
  | mk (S W D O R E H C P N : BHist) : RegularCauchyOscillationCriterionUp
  deriving DecidableEq

def regularCauchyOscillationCriterionEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyOscillationCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyOscillationCriterionEncodeBHist h

def regularCauchyOscillationCriterionDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyOscillationCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyOscillationCriterionDecodeBHist tail)

private theorem RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyOscillationCriterionFields :
    RegularCauchyOscillationCriterionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyOscillationCriterionUp.mk S W D O R E H C P N =>
      [S, W, D, O, R, E, H, C, P, N]

def regularCauchyOscillationCriterionToEventFlow :
    RegularCauchyOscillationCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyOscillationCriterionFields x).map
    regularCauchyOscillationCriterionEncodeBHist

private def regularCauchyOscillationCriterionEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyOscillationCriterionEventAt index rest

def regularCauchyOscillationCriterionFromEventFlow :
    EventFlow → Option RegularCauchyOscillationCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyOscillationCriterionUp.mk
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 0 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 1 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 2 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 3 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 4 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 5 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 6 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 7 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 8 ef))
        (regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEventAt 9 ef)))

private theorem RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyOscillationCriterionUp,
      regularCauchyOscillationCriterionFromEventFlow
          (regularCauchyOscillationCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D O R E H C P N =>
      change
        some
            (RegularCauchyOscillationCriterionUp.mk
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist S))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist W))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist D))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist O))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist R))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist E))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist H))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist C))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist P))
              (regularCauchyOscillationCriterionDecodeBHist
                (regularCauchyOscillationCriterionEncodeBHist N))) =
          some (RegularCauchyOscillationCriterionUp.mk S W D O R E H C P N)
      rw [RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode S,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode W,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode D,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode O,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode R,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode E,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode H,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode C,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode P,
        RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode N]

private theorem regularCauchyOscillationCriterionToEventFlow_injective
    {x y : RegularCauchyOscillationCriterionUp} :
    regularCauchyOscillationCriterionToEventFlow x =
        regularCauchyOscillationCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyOscillationCriterionFromEventFlow
          (regularCauchyOscillationCriterionToEventFlow x) =
        regularCauchyOscillationCriterionFromEventFlow
          (regularCauchyOscillationCriterionToEventFlow y) :=
    congrArg regularCauchyOscillationCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem regularCauchyOscillationCriterion_field_faithful :
    ∀ x y : RegularCauchyOscillationCriterionUp,
      regularCauchyOscillationCriterionFields x =
          regularCauchyOscillationCriterionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 D1 O1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 D2 O2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyOscillationCriterionBHistCarrier :
    BHistCarrier RegularCauchyOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyOscillationCriterionToEventFlow
  fromEventFlow := regularCauchyOscillationCriterionFromEventFlow

instance regularCauchyOscillationCriterionChapterTasteGate :
    ChapterTasteGate RegularCauchyOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyOscillationCriterionFromEventFlow
          (regularCauchyOscillationCriterionToEventFlow x) =
        some x
    exact RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyOscillationCriterionToEventFlow_injective heq)

instance regularCauchyOscillationCriterionFieldFaithful :
    FieldFaithful RegularCauchyOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyOscillationCriterionFields
  field_faithful := regularCauchyOscillationCriterion_field_faithful

instance regularCauchyOscillationCriterionNontrivial :
    Nontrivial RegularCauchyOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyOscillationCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyOscillationCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyOscillationCriterionDecodeBHist
          (regularCauchyOscillationCriterionEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyOscillationCriterionUp,
        regularCauchyOscillationCriterionFromEventFlow
            (regularCauchyOscillationCriterionToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyOscillationCriterionUp,
        regularCauchyOscillationCriterionToEventFlow x =
            regularCauchyOscillationCriterionToEventFlow y →
          x = y) ∧
      regularCauchyOscillationCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_decode,
      RegularCauchyOscillationCriterionTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => regularCauchyOscillationCriterionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyOscillationCriterionUp
