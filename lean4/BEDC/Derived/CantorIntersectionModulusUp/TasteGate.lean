import BEDC.Derived.CantorIntersectionModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorIntersectionModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def CantorIntersectionModulusTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CantorIntersectionModulusTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CantorIntersectionModulusTasteGate_single_carrier_alignment_encodeBHist h

def cantorIntersectionModulusEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  CantorIntersectionModulusTasteGate_single_carrier_alignment_encodeBHist

def CantorIntersectionModulusTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CantorIntersectionModulusTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CantorIntersectionModulusTasteGate_single_carrier_alignment_decodeBHist tail)

def cantorIntersectionModulusDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  CantorIntersectionModulusTasteGate_single_carrier_alignment_decodeBHist

private theorem CantorIntersectionModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cantorIntersectionModulusDecodeBHist (cantorIntersectionModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CantorIntersectionModulusTasteGate_single_carrier_alignment_fields :
    BEDC.Derived.CantorIntersectionModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CantorIntersectionModulusUp.mk L B D S R E F H C P N =>
      [L, B, D, S, R, E, F, H, C, P, N]

def cantorIntersectionModulusToEventFlow :
    BEDC.Derived.CantorIntersectionModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CantorIntersectionModulusTasteGate_single_carrier_alignment_fields x).map
      cantorIntersectionModulusEncodeBHist

private def CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt index rest

def cantorIntersectionModulusFromEventFlow :
    EventFlow → Option BEDC.Derived.CantorIntersectionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BEDC.Derived.CantorIntersectionModulusUp.mk
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 0 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 1 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 2 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 3 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 4 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 5 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 6 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 7 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 8 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 9 ef))
        (cantorIntersectionModulusDecodeBHist
          (CantorIntersectionModulusTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem CantorIntersectionModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.CantorIntersectionModulusUp,
      cantorIntersectionModulusFromEventFlow (cantorIntersectionModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L B D S R E F H C P N =>
      change
        some
          (BEDC.Derived.CantorIntersectionModulusUp.mk
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist L))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist B))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist D))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist S))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist R))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist E))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist F))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist H))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist C))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist P))
            (cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist N))) =
          some (BEDC.Derived.CantorIntersectionModulusUp.mk L B D S R E F H C P N)
      rw [CantorIntersectionModulusTasteGate_single_carrier_alignment_decode L,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode B,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode D,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode S,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode R,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode E,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode F,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode H,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode C,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode P,
        CantorIntersectionModulusTasteGate_single_carrier_alignment_decode N]

private theorem CantorIntersectionModulusTasteGate_single_carrier_alignment_injective
    {x y : BEDC.Derived.CantorIntersectionModulusUp} :
    cantorIntersectionModulusToEventFlow x = cantorIntersectionModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorIntersectionModulusFromEventFlow (cantorIntersectionModulusToEventFlow x) =
        cantorIntersectionModulusFromEventFlow (cantorIntersectionModulusToEventFlow y) :=
    congrArg cantorIntersectionModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CantorIntersectionModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CantorIntersectionModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem CantorIntersectionModulusTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BEDC.Derived.CantorIntersectionModulusUp,
      CantorIntersectionModulusTasteGate_single_carrier_alignment_fields x =
        CantorIntersectionModulusTasteGate_single_carrier_alignment_fields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ B₁ D₁ S₁ R₁ E₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ B₂ D₂ S₂ R₂ E₂ F₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cantorIntersectionModulusBHistCarrier :
    BHistCarrier BEDC.Derived.CantorIntersectionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorIntersectionModulusToEventFlow
  fromEventFlow := cantorIntersectionModulusFromEventFlow

instance cantorIntersectionModulusChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CantorIntersectionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cantorIntersectionModulusFromEventFlow (cantorIntersectionModulusToEventFlow x) =
        some x
    exact CantorIntersectionModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorIntersectionModulusTasteGate_single_carrier_alignment_injective heq)

instance cantorIntersectionModulusFieldFaithful :
    FieldFaithful BEDC.Derived.CantorIntersectionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CantorIntersectionModulusTasteGate_single_carrier_alignment_fields
  field_faithful :=
    CantorIntersectionModulusTasteGate_single_carrier_alignment_field_faithful

instance cantorIntersectionModulusNontrivial :
    Nontrivial BEDC.Derived.CantorIntersectionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BEDC.Derived.CantorIntersectionModulusUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BEDC.Derived.CantorIntersectionModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BEDC.Derived.CantorIntersectionModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cantorIntersectionModulusChapterTasteGate

theorem CantorIntersectionModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BEDC.Derived.CantorIntersectionModulusUp) ∧
      Nonempty (ChapterTasteGate BEDC.Derived.CantorIntersectionModulusUp) ∧
        Nonempty (FieldFaithful BEDC.Derived.CantorIntersectionModulusUp) ∧
          (∀ h : BHist,
            cantorIntersectionModulusDecodeBHist
              (cantorIntersectionModulusEncodeBHist h) = h) ∧
            cantorIntersectionModulusEncodeBHist BHist.Empty = ([] : List BMark) ∧
              (∃ x y : BEDC.Derived.CantorIntersectionModulusUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨cantorIntersectionModulusBHistCarrier⟩,
      ⟨⟨cantorIntersectionModulusChapterTasteGate⟩,
        ⟨⟨cantorIntersectionModulusFieldFaithful⟩,
          CantorIntersectionModulusTasteGate_single_carrier_alignment_decode,
          rfl,
          ⟨(cantorIntersectionModulusNontrivial.witness_pair).1,
            (cantorIntersectionModulusNontrivial.witness_pair).2.1,
            (cantorIntersectionModulusNontrivial.witness_pair).2.2⟩⟩⟩⟩

end BEDC.Derived.CantorIntersectionModulusUp
