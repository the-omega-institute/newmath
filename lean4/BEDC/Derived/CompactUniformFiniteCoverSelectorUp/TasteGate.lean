import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformFiniteCoverSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformFiniteCoverSelectorUp : Type where
  | mk (K F E M R U H C P N : BHist) : CompactUniformFiniteCoverSelectorUp
  deriving DecidableEq

def compactUniformFiniteCoverSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformFiniteCoverSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformFiniteCoverSelectorEncodeBHist h

def compactUniformFiniteCoverSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformFiniteCoverSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformFiniteCoverSelectorDecodeBHist tail)

private theorem CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformFiniteCoverSelectorFields :
    CompactUniformFiniteCoverSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformFiniteCoverSelectorUp.mk K F E M R U H C P N =>
      [K, F, E, M, R, U, H, C, P, N]

def compactUniformFiniteCoverSelectorToEventFlow :
    CompactUniformFiniteCoverSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformFiniteCoverSelectorFields x).map
      compactUniformFiniteCoverSelectorEncodeBHist

private def compactUniformFiniteCoverSelectorEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactUniformFiniteCoverSelectorEventAtDefault index rest

def compactUniformFiniteCoverSelectorFromEventFlow
    (ef : EventFlow) : Option CompactUniformFiniteCoverSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformFiniteCoverSelectorUp.mk
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 0 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 1 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 2 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 3 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 4 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 5 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 6 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 7 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 8 ef))
      (compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEventAtDefault 9 ef)))

private theorem CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformFiniteCoverSelectorUp,
      compactUniformFiniteCoverSelectorFromEventFlow
        (compactUniformFiniteCoverSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F E M R U H C P N =>
      change
        some
          (CompactUniformFiniteCoverSelectorUp.mk
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist K))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist F))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist E))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist M))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist R))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist U))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist H))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist C))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist P))
            (compactUniformFiniteCoverSelectorDecodeBHist
              (compactUniformFiniteCoverSelectorEncodeBHist N))) =
          some (CompactUniformFiniteCoverSelectorUp.mk K F E M R U H C P N)
      rw [CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode K,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode F,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode E,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode M,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode R,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode U,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode H,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode C,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode P,
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformFiniteCoverSelectorUp} :
    compactUniformFiniteCoverSelectorToEventFlow x =
      compactUniformFiniteCoverSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformFiniteCoverSelectorFromEventFlow
          (compactUniformFiniteCoverSelectorToEventFlow x) =
        compactUniformFiniteCoverSelectorFromEventFlow
          (compactUniformFiniteCoverSelectorToEventFlow y) :=
    congrArg compactUniformFiniteCoverSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactUniformFiniteCoverSelectorUp,
      compactUniformFiniteCoverSelectorFields x = compactUniformFiniteCoverSelectorFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 E1 M1 R1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 E2 M2 R2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactUniformFiniteCoverSelectorBHistCarrier :
    BHistCarrier CompactUniformFiniteCoverSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformFiniteCoverSelectorToEventFlow
  fromEventFlow := compactUniformFiniteCoverSelectorFromEventFlow

instance compactUniformFiniteCoverSelectorChapterTasteGate :
    ChapterTasteGate CompactUniformFiniteCoverSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformFiniteCoverSelectorFromEventFlow
        (compactUniformFiniteCoverSelectorToEventFlow x) = some x
    exact CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance compactUniformFiniteCoverSelectorFieldFaithful :
    FieldFaithful CompactUniformFiniteCoverSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformFiniteCoverSelectorFields
  field_faithful := CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_fields

instance compactUniformFiniteCoverSelectorNontrivial :
    Nontrivial CompactUniformFiniteCoverSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformFiniteCoverSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompactUniformFiniteCoverSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactUniformFiniteCoverSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactUniformFiniteCoverSelectorChapterTasteGate

theorem CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactUniformFiniteCoverSelectorDecodeBHist
        (compactUniformFiniteCoverSelectorEncodeBHist h) = h) ∧
      (forall x : CompactUniformFiniteCoverSelectorUp,
        compactUniformFiniteCoverSelectorFromEventFlow
          (compactUniformFiniteCoverSelectorToEventFlow x) = some x) ∧
        (forall x y : CompactUniformFiniteCoverSelectorUp,
          compactUniformFiniteCoverSelectorToEventFlow x =
            compactUniformFiniteCoverSelectorToEventFlow y -> x = y) ∧
          compactUniformFiniteCoverSelectorEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_decode,
      CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompactUniformFiniteCoverSelectorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactUniformFiniteCoverSelectorUp
