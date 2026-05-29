import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterRefinementUp : Type where
  | mk (F S W D R E H C P N : BHist) : RegularCauchyFilterRefinementUp
  deriving DecidableEq

def regularCauchyFilterRefinementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterRefinementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterRefinementEncodeBHist h

def regularCauchyFilterRefinementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterRefinementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterRefinementDecodeBHist tail)

private theorem RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFilterRefinementFields :
    RegularCauchyFilterRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterRefinementUp.mk F S W D R E H C P N =>
      [F, S, W, D, R, E, H, C, P, N]

def regularCauchyFilterRefinementToEventFlow :
    RegularCauchyFilterRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyFilterRefinementFields x).map
      regularCauchyFilterRefinementEncodeBHist

private def regularCauchyFilterRefinementEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyFilterRefinementEventAt index rest

def regularCauchyFilterRefinementFromEventFlow (ef : EventFlow) :
    Option RegularCauchyFilterRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFilterRefinementUp.mk
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 0 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 1 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 2 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 3 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 4 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 5 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 6 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 7 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 8 ef))
      (regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEventAt 9 ef)))

private theorem RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyFilterRefinementUp) :
    regularCauchyFilterRefinementFromEventFlow
        (regularCauchyFilterRefinementToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F S W D R E H C P N =>
      change
        some
          (RegularCauchyFilterRefinementUp.mk
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist F))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist S))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist W))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist D))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist R))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist E))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist H))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist C))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist P))
            (regularCauchyFilterRefinementDecodeBHist
              (regularCauchyFilterRefinementEncodeBHist N))) =
          some (RegularCauchyFilterRefinementUp.mk F S W D R E H C P N)
      rw [RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode F,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode S,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode W,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode D,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode R,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode E,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode H,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode C,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode P,
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFilterRefinementUp} :
    regularCauchyFilterRefinementToEventFlow x =
        regularCauchyFilterRefinementToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterRefinementFromEventFlow
          (regularCauchyFilterRefinementToEventFlow x) =
        regularCauchyFilterRefinementFromEventFlow
          (regularCauchyFilterRefinementToEventFlow y) :=
    congrArg regularCauchyFilterRefinementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyFilterRefinementUp,
      regularCauchyFilterRefinementFields x = regularCauchyFilterRefinementFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ S₁ W₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ S₂ W₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyFilterRefinementBHistCarrier :
    BHistCarrier RegularCauchyFilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterRefinementToEventFlow
  fromEventFlow := regularCauchyFilterRefinementFromEventFlow

instance regularCauchyFilterRefinementChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyFilterRefinementFromEventFlow
      (regularCauchyFilterRefinementToEventFlow x) = some x
    exact RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance regularCauchyFilterRefinementFieldFaithful :
    FieldFaithful RegularCauchyFilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyFilterRefinementFields
  field_faithful :=
    RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyFilterRefinementNontrivial :
    Nontrivial RegularCauchyFilterRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyFilterRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyFilterRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyFilterRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFilterRefinementChapterTasteGate

theorem RegularCauchyFilterRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyFilterRefinementDecodeBHist
        (regularCauchyFilterRefinementEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyFilterRefinementUp,
        regularCauchyFilterRefinementFromEventFlow
          (regularCauchyFilterRefinementToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyFilterRefinementUp,
        regularCauchyFilterRefinementToEventFlow x =
            regularCauchyFilterRefinementToEventFlow y →
          x = y) ∧
      regularCauchyFilterRefinementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_decode,
      RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        RegularCauchyFilterRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.RegularCauchyFilterRefinementUp
