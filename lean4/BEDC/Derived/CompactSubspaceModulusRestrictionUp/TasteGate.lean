import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactSubspaceModulusRestrictionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactSubspaceModulusRestrictionUp : Type where
  | mk (K S F M U H C P N : BHist) : CompactSubspaceModulusRestrictionUp
  deriving DecidableEq

def compactSubspaceModulusRestrictionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactSubspaceModulusRestrictionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactSubspaceModulusRestrictionEncodeBHist h

def compactSubspaceModulusRestrictionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactSubspaceModulusRestrictionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactSubspaceModulusRestrictionDecodeBHist tail)

private theorem compactSubspaceModulusRestrictionDecode_encode :
    ∀ h : BHist,
      compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactSubspaceModulusRestrictionToEventFlow :
    CompactSubspaceModulusRestrictionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactSubspaceModulusRestrictionUp.mk K S F M U H C P N =>
      [compactSubspaceModulusRestrictionEncodeBHist K,
        compactSubspaceModulusRestrictionEncodeBHist S,
        compactSubspaceModulusRestrictionEncodeBHist F,
        compactSubspaceModulusRestrictionEncodeBHist M,
        compactSubspaceModulusRestrictionEncodeBHist U,
        compactSubspaceModulusRestrictionEncodeBHist H,
        compactSubspaceModulusRestrictionEncodeBHist C,
        compactSubspaceModulusRestrictionEncodeBHist P,
        compactSubspaceModulusRestrictionEncodeBHist N]

private def compactSubspaceModulusRestrictionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactSubspaceModulusRestrictionEventAtDefault index rest

def compactSubspaceModulusRestrictionFromEventFlow :
    EventFlow → Option CompactSubspaceModulusRestrictionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactSubspaceModulusRestrictionUp.mk
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 0 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 1 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 2 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 3 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 4 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 5 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 6 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 7 ef))
        (compactSubspaceModulusRestrictionDecodeBHist
          (compactSubspaceModulusRestrictionEventAtDefault 8 ef)))

private theorem compactSubspaceModulusRestriction_round_trip :
    ∀ x : CompactSubspaceModulusRestrictionUp,
      compactSubspaceModulusRestrictionFromEventFlow
          (compactSubspaceModulusRestrictionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K S F M U H C P N =>
      change
        some
            (CompactSubspaceModulusRestrictionUp.mk
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist K))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist S))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist F))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist M))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist U))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist H))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist C))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist P))
              (compactSubspaceModulusRestrictionDecodeBHist
                (compactSubspaceModulusRestrictionEncodeBHist N))) =
          some (CompactSubspaceModulusRestrictionUp.mk K S F M U H C P N)
      rw [compactSubspaceModulusRestrictionDecode_encode K,
        compactSubspaceModulusRestrictionDecode_encode S,
        compactSubspaceModulusRestrictionDecode_encode F,
        compactSubspaceModulusRestrictionDecode_encode M,
        compactSubspaceModulusRestrictionDecode_encode U,
        compactSubspaceModulusRestrictionDecode_encode H,
        compactSubspaceModulusRestrictionDecode_encode C,
        compactSubspaceModulusRestrictionDecode_encode P,
        compactSubspaceModulusRestrictionDecode_encode N]

private theorem compactSubspaceModulusRestrictionToEventFlow_injective
    {x y : CompactSubspaceModulusRestrictionUp} :
    compactSubspaceModulusRestrictionToEventFlow x =
        compactSubspaceModulusRestrictionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactSubspaceModulusRestrictionFromEventFlow
          (compactSubspaceModulusRestrictionToEventFlow x) =
        compactSubspaceModulusRestrictionFromEventFlow
          (compactSubspaceModulusRestrictionToEventFlow y) :=
    congrArg compactSubspaceModulusRestrictionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactSubspaceModulusRestriction_round_trip x).symm
      (Eq.trans hread (compactSubspaceModulusRestriction_round_trip y)))

def compactSubspaceModulusRestrictionFields :
    CompactSubspaceModulusRestrictionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactSubspaceModulusRestrictionUp.mk K S F M U H C P N => [K, S, F, M, U, H, C, P, N]

private theorem compactSubspaceModulusRestriction_field_faithful :
    ∀ x y : CompactSubspaceModulusRestrictionUp,
      compactSubspaceModulusRestrictionFields x =
          compactSubspaceModulusRestrictionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 S1 F1 M1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 S2 F2 M2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactSubspaceModulusRestrictionBHistCarrier :
    BHistCarrier CompactSubspaceModulusRestrictionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactSubspaceModulusRestrictionToEventFlow
  fromEventFlow := compactSubspaceModulusRestrictionFromEventFlow

instance compactSubspaceModulusRestrictionChapterTasteGate :
    ChapterTasteGate CompactSubspaceModulusRestrictionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactSubspaceModulusRestrictionFromEventFlow
          (compactSubspaceModulusRestrictionToEventFlow x) =
        some x
    exact compactSubspaceModulusRestriction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactSubspaceModulusRestrictionToEventFlow_injective heq)

instance compactSubspaceModulusRestrictionFieldFaithful :
    FieldFaithful CompactSubspaceModulusRestrictionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactSubspaceModulusRestrictionFields
  field_faithful := compactSubspaceModulusRestriction_field_faithful

theorem CompactSubspaceModulusRestrictionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        compactSubspaceModulusRestrictionDecodeBHist
            (compactSubspaceModulusRestrictionEncodeBHist h) =
          h) ∧
      (∀ x : CompactSubspaceModulusRestrictionUp,
        compactSubspaceModulusRestrictionFromEventFlow
            (compactSubspaceModulusRestrictionToEventFlow x) =
          some x) ∧
      (∀ x y : CompactSubspaceModulusRestrictionUp,
        compactSubspaceModulusRestrictionToEventFlow x =
            compactSubspaceModulusRestrictionToEventFlow y →
          x = y) ∧
      compactSubspaceModulusRestrictionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨compactSubspaceModulusRestrictionDecode_encode,
      compactSubspaceModulusRestriction_round_trip,
      fun _ _ heq => compactSubspaceModulusRestrictionToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CompactSubspaceModulusRestrictionUp
