import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformContinuityModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformContinuityModulusUp : Type where
  | mk (K F M D R H C P N : BHist) : CompactUniformContinuityModulusUp
  deriving DecidableEq

def compactUniformContinuityModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformContinuityModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformContinuityModulusEncodeBHist h

def compactUniformContinuityModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformContinuityModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformContinuityModulusDecodeBHist tail)

private theorem CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformContinuityModulusDecodeBHist
        (compactUniformContinuityModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformContinuityModulusFields :
    CompactUniformContinuityModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformContinuityModulusUp.mk K F M D R H C P N =>
      [K, F, M, D, R, H, C, P, N]

def compactUniformContinuityModulusToEventFlow :
    CompactUniformContinuityModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformContinuityModulusFields x).map
      compactUniformContinuityModulusEncodeBHist

private def compactUniformContinuityModulusEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformContinuityModulusEventAtDefault index rest

def compactUniformContinuityModulusFromEventFlow :
    EventFlow → Option CompactUniformContinuityModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CompactUniformContinuityModulusUp.mk
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 0 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 1 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 2 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 3 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 4 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 5 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 6 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 7 ef))
          (compactUniformContinuityModulusDecodeBHist
            (compactUniformContinuityModulusEventAtDefault 8 ef)))

private theorem CompactUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformContinuityModulusUp,
      compactUniformContinuityModulusFromEventFlow
          (compactUniformContinuityModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F M D R H C P N =>
      change
        some
          (CompactUniformContinuityModulusUp.mk
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist K))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist F))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist M))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist D))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist R))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist H))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist C))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist P))
            (compactUniformContinuityModulusDecodeBHist
              (compactUniformContinuityModulusEncodeBHist N))) =
          some (CompactUniformContinuityModulusUp.mk K F M D R H C P N)
      rw [CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode K,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode F,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode M,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode D,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode R,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode H,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode C,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode P,
        CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformContinuityModulusToEventFlow_injective
    {x y : CompactUniformContinuityModulusUp} :
    compactUniformContinuityModulusToEventFlow x =
        compactUniformContinuityModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformContinuityModulusFromEventFlow
          (compactUniformContinuityModulusToEventFlow x) =
        compactUniformContinuityModulusFromEventFlow
          (compactUniformContinuityModulusToEventFlow y) :=
    congrArg compactUniformContinuityModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactUniformContinuityModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactUniformContinuityModulusUp,
      compactUniformContinuityModulusFields x = compactUniformContinuityModulusFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 M1 D1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 M2 D2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactUniformContinuityModulusBHistCarrier :
    BHistCarrier CompactUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformContinuityModulusToEventFlow
  fromEventFlow := compactUniformContinuityModulusFromEventFlow

instance compactUniformContinuityModulusChapterTasteGate :
    ChapterTasteGate CompactUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformContinuityModulusFromEventFlow
          (compactUniformContinuityModulusToEventFlow x) =
        some x
    exact CompactUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactUniformContinuityModulusToEventFlow_injective heq)

instance compactUniformContinuityModulusFieldFaithful :
    FieldFaithful CompactUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformContinuityModulusFields
  field_faithful := CompactUniformContinuityModulusTasteGate_single_carrier_alignment_fields

instance compactUniformContinuityModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CompactUniformContinuityModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformContinuityModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformContinuityModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactUniformContinuityModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformContinuityModulusChapterTasteGate

theorem CompactUniformContinuityModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactUniformContinuityModulusUp) ∧
      Nonempty (FieldFaithful CompactUniformContinuityModulusUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactUniformContinuityModulusUp) ∧
      (∀ h : BHist,
        compactUniformContinuityModulusDecodeBHist
          (compactUniformContinuityModulusEncodeBHist h) = h) ∧
      (∀ x : CompactUniformContinuityModulusUp,
        compactUniformContinuityModulusFromEventFlow
            (compactUniformContinuityModulusToEventFlow x) =
          some x) ∧
      (∀ x y : CompactUniformContinuityModulusUp,
        compactUniformContinuityModulusToEventFlow x =
            compactUniformContinuityModulusToEventFlow y →
          x = y) ∧
      compactUniformContinuityModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨compactUniformContinuityModulusChapterTasteGate⟩,
      ⟨compactUniformContinuityModulusFieldFaithful⟩,
      ⟨compactUniformContinuityModulusNontrivial⟩,
      CompactUniformContinuityModulusTasteGate_single_carrier_alignment_decode,
      CompactUniformContinuityModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompactUniformContinuityModulusToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactUniformContinuityModulusUp
