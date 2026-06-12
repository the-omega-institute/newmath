import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactModulusOscillationRouterUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactModulusOscillationRouterUp : Type where
  | mk (K M F O Q D S A U H C P N : BHist) : CompactModulusOscillationRouterUp
  deriving DecidableEq

def compactModulusOscillationRouterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactModulusOscillationRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactModulusOscillationRouterEncodeBHist h

def compactModulusOscillationRouterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactModulusOscillationRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactModulusOscillationRouterDecodeBHist tail)

private theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactModulusOscillationRouterDecodeBHist
          (compactModulusOscillationRouterEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactModulusOscillationRouterFields :
    CompactModulusOscillationRouterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactModulusOscillationRouterUp.mk K M F O Q D S A U H C P N =>
      [K, M, F, O, Q, D, S, A, U, H, C, P, N]

def compactModulusOscillationRouterToEventFlow :
    CompactModulusOscillationRouterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactModulusOscillationRouterFields x).map
      compactModulusOscillationRouterEncodeBHist

private def compactModulusOscillationRouterEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactModulusOscillationRouterEventAt index rest

def compactModulusOscillationRouterFromEventFlow (ef : EventFlow) :
    Option CompactModulusOscillationRouterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactModulusOscillationRouterUp.mk
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 0 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 1 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 2 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 3 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 4 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 5 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 6 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 7 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 8 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 9 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 10 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 11 ef))
      (compactModulusOscillationRouterDecodeBHist
        (compactModulusOscillationRouterEventAt 12 ef)))

private theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip
    (x : CompactModulusOscillationRouterUp) :
    compactModulusOscillationRouterFromEventFlow
        (compactModulusOscillationRouterToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K M F O Q D S A U H C P N =>
      change
        some
          (CompactModulusOscillationRouterUp.mk
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist K))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist M))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist F))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist O))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist Q))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist D))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist S))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist A))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist U))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist H))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist C))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist P))
            (compactModulusOscillationRouterDecodeBHist
              (compactModulusOscillationRouterEncodeBHist N))) =
          some (CompactModulusOscillationRouterUp.mk K M F O Q D S A U H C P N)
      rw [CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode K,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode M,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode F,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode O,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode Q,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode D,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode S,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode A,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode U,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode H,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode C,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode P,
        CompactModulusOscillationRouterTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactModulusOscillationRouterUp} :
    compactModulusOscillationRouterToEventFlow x =
        compactModulusOscillationRouterToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactModulusOscillationRouterFromEventFlow
          (compactModulusOscillationRouterToEventFlow x) =
        compactModulusOscillationRouterFromEventFlow
          (compactModulusOscillationRouterToEventFlow y) :=
    congrArg compactModulusOscillationRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CompactModulusOscillationRouterUp,
      compactModulusOscillationRouterFields x = compactModulusOscillationRouterFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ M₁ F₁ O₁ Q₁ D₁ S₁ A₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ M₂ F₂ O₂ Q₂ D₂ S₂ A₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compactModulusOscillationRouterBHistCarrier :
    BHistCarrier CompactModulusOscillationRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactModulusOscillationRouterToEventFlow
  fromEventFlow := compactModulusOscillationRouterFromEventFlow

instance compactModulusOscillationRouterChapterTasteGate :
    ChapterTasteGate CompactModulusOscillationRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactModulusOscillationRouterFromEventFlow
          (compactModulusOscillationRouterToEventFlow x) =
        some x
    exact CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactModulusOscillationRouterTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance compactModulusOscillationRouterFieldFaithful :
    FieldFaithful CompactModulusOscillationRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactModulusOscillationRouterFields
  field_faithful :=
    CompactModulusOscillationRouterTasteGate_single_carrier_alignment_fields_faithful

instance compactModulusOscillationRouterNontrivial :
    Nontrivial CompactModulusOscillationRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactModulusOscillationRouterUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactModulusOscillationRouterUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CompactModulusOscillationRouterTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompactModulusOscillationRouterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactModulusOscillationRouterChapterTasteGate

theorem CompactModulusOscillationRouterTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompactModulusOscillationRouterUp) ∧
      Nonempty (ChapterTasteGate CompactModulusOscillationRouterUp) ∧
        (∀ x : CompactModulusOscillationRouterUp,
          compactModulusOscillationRouterFromEventFlow
              (compactModulusOscillationRouterToEventFlow x) =
            some x) ∧
          compactModulusOscillationRouterEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨compactModulusOscillationRouterBHistCarrier⟩,
      ⟨compactModulusOscillationRouterChapterTasteGate⟩,
      CompactModulusOscillationRouterTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CompactModulusOscillationRouterUp.TasteGate
