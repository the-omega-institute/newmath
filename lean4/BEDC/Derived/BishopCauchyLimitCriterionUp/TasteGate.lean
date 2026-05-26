import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyLimitCriterionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyLimitCriterionUp : Type where
  | mk (S R D M F E H C P N : BHist) : BishopCauchyLimitCriterionUp
  deriving DecidableEq

def bishopCauchyLimitCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyLimitCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyLimitCriterionEncodeBHist h

def bishopCauchyLimitCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyLimitCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyLimitCriterionDecodeBHist tail)

private theorem BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyLimitCriterionFields :
    BishopCauchyLimitCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyLimitCriterionUp.mk S R D M F E H C P N => [S, R, D, M, F, E, H, C, P, N]

def bishopCauchyLimitCriterionToEventFlow :
    BishopCauchyLimitCriterionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopCauchyLimitCriterionFields x).map bishopCauchyLimitCriterionEncodeBHist

private def bishopCauchyLimitCriterionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyLimitCriterionEventAt index rest

def bishopCauchyLimitCriterionFromEventFlow
    (ef : EventFlow) : Option BishopCauchyLimitCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopCauchyLimitCriterionUp.mk
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 0 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 1 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 2 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 3 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 4 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 5 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 6 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 7 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 8 ef))
      (bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEventAt 9 ef)))

private theorem BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_round_trip
    (x : BishopCauchyLimitCriterionUp) :
    bishopCauchyLimitCriterionFromEventFlow (bishopCauchyLimitCriterionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S R D M F E H C P N =>
      change
        some
          (BishopCauchyLimitCriterionUp.mk
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist S))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist R))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist D))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist M))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist F))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist E))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist H))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist C))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist P))
            (bishopCauchyLimitCriterionDecodeBHist
              (bishopCauchyLimitCriterionEncodeBHist N))) =
          some (BishopCauchyLimitCriterionUp.mk S R D M F E H C P N)
      rw [BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode S,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode R,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode D,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode M,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode F,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode E,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode H,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode C,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode P,
        BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode N]

private theorem BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCauchyLimitCriterionUp} :
    bishopCauchyLimitCriterionToEventFlow x = bishopCauchyLimitCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyLimitCriterionFromEventFlow (bishopCauchyLimitCriterionToEventFlow x) =
        bishopCauchyLimitCriterionFromEventFlow (bishopCauchyLimitCriterionToEventFlow y) :=
    congrArg bishopCauchyLimitCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopCauchyLimitCriterionUp,
      bishopCauchyLimitCriterionFields x = bishopCauchyLimitCriterionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 D1 M1 F1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 M2 F2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopCauchyLimitCriterionBHistCarrier :
    BHistCarrier BishopCauchyLimitCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyLimitCriterionToEventFlow
  fromEventFlow := bishopCauchyLimitCriterionFromEventFlow

instance bishopCauchyLimitCriterionChapterTasteGate :
    ChapterTasteGate BishopCauchyLimitCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyLimitCriterionFromEventFlow (bishopCauchyLimitCriterionToEventFlow x) =
        some x
    exact BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopCauchyLimitCriterionFieldFaithful :
    FieldFaithful BishopCauchyLimitCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopCauchyLimitCriterionFields
  field_faithful := BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_fields

instance bishopCauchyLimitCriterionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial BishopCauchyLimitCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopCauchyLimitCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopCauchyLimitCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BishopCauchyLimitCriterionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BishopCauchyLimitCriterionUp) ∧
      Nonempty (FieldFaithful BishopCauchyLimitCriterionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial BishopCauchyLimitCriterionUp) ∧
      (∀ h : BHist,
        bishopCauchyLimitCriterionDecodeBHist (bishopCauchyLimitCriterionEncodeBHist h) =
          h) ∧
      (∀ x : BishopCauchyLimitCriterionUp,
        bishopCauchyLimitCriterionFromEventFlow
            (bishopCauchyLimitCriterionToEventFlow x) =
          some x) ∧
      bishopCauchyLimitCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨bishopCauchyLimitCriterionChapterTasteGate⟩,
      ⟨bishopCauchyLimitCriterionFieldFaithful⟩,
      ⟨bishopCauchyLimitCriterionNontrivial⟩,
      BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_decode,
      BishopCauchyLimitCriterionTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.BishopCauchyLimitCriterionUp.TasteGate
