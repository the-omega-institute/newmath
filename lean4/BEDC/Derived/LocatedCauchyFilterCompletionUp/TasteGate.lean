import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyFilterCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyFilterCompletionUp : Type where
  | mk (F L W R D E H C P N : BHist) : LocatedCauchyFilterCompletionUp
  deriving DecidableEq

def LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist h

def LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
          (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields :
    LocatedCauchyFilterCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyFilterCompletionUp.mk F L W R D E H C P N =>
      [F, L, W, R, D, E, H, C, P, N]

def LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow :
    LocatedCauchyFilterCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields x).map
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist

private def LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt index rest

def LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option LocatedCauchyFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCauchyFilterCompletionUp.mk
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip
    (x : LocatedCauchyFilterCompletionUp) :
    LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fromEventFlow
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F L W R D E H C P N =>
      change
        some
          (LocatedCauchyFilterCompletionUp.mk
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist F))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist L))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist W))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist R))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist D))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist E))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist H))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist C))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist P))
            (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
              (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (LocatedCauchyFilterCompletionUp.mk F L W R D E H C P N)
      rw [LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode F,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode L,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode W,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode R,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode D,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode E,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode H,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode C,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode P,
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCauchyFilterCompletionUp} :
    LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow x =
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LocatedCauchyFilterCompletionUp,
      LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields x =
          LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ L₁ W₁ R₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ L₂ W₂ R₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier LocatedCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fromEventFlow

instance LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate LocatedCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful LocatedCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields
  field_faithful :=
    LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields_faithful

instance LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial LocatedCauchyFilterCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCauchyFilterCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCauchyFilterCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedCauchyFilterCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_ChapterTasteGate

theorem LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decodeBHist
          (LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_fields
          (LocatedCauchyFilterCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedCauchyFilterCompletionTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.LocatedCauchyFilterCompletionUp
