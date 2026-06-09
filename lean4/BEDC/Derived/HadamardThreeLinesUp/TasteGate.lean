import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HadamardThreeLinesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HadamardThreeLinesUp : Type where
  | mk (S F Y0 Y1 Y B M E Hs C P N : BHist) : HadamardThreeLinesUp
  deriving DecidableEq

def hadamardThreeLinesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hadamardThreeLinesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hadamardThreeLinesEncodeBHist h

def hadamardThreeLinesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hadamardThreeLinesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hadamardThreeLinesDecodeBHist tail)

private theorem HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hadamardThreeLinesFields : HadamardThreeLinesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HadamardThreeLinesUp.mk S F Y0 Y1 Y B M E Hs C P N =>
      [S, F, Y0, Y1, Y, B, M, E, Hs, C, P, N]

def hadamardThreeLinesToEventFlow : HadamardThreeLinesUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hadamardThreeLinesFields x).map hadamardThreeLinesEncodeBHist

private def HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault index rest

def hadamardThreeLinesFromEventFlow (ef : EventFlow) : Option HadamardThreeLinesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HadamardThreeLinesUp.mk
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (hadamardThreeLinesDecodeBHist
        (HadamardThreeLinesTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem HadamardThreeLinesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HadamardThreeLinesUp,
      hadamardThreeLinesFromEventFlow (hadamardThreeLinesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F Y0 Y1 Y B M E Hs C P N =>
      change
        some
            (HadamardThreeLinesUp.mk
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist S))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist F))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist Y0))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist Y1))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist Y))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist B))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist M))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist E))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist Hs))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist C))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist P))
              (hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist N))) =
          some (HadamardThreeLinesUp.mk S F Y0 Y1 Y B M E Hs C P N)
      rw [HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode S,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode F,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode Y0,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode Y1,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode Y,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode B,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode M,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode E,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode Hs,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode C,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode P,
        HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode N]

private theorem HadamardThreeLinesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HadamardThreeLinesUp} :
    hadamardThreeLinesToEventFlow x = hadamardThreeLinesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hadamardThreeLinesFromEventFlow (hadamardThreeLinesToEventFlow x) =
        hadamardThreeLinesFromEventFlow (hadamardThreeLinesToEventFlow y) :=
    congrArg hadamardThreeLinesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HadamardThreeLinesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HadamardThreeLinesTasteGate_single_carrier_alignment_round_trip y)))

private theorem HadamardThreeLinesTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : HadamardThreeLinesUp,
      hadamardThreeLinesFields x = hadamardThreeLinesFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 F1 Y01 Y11 Y1 B1 M1 E1 Hs1 C1 P1 N1 =>
      cases y with
      | mk S2 F2 Y02 Y12 Y2 B2 M2 E2 Hs2 C2 P2 N2 =>
          cases hfields
          rfl

instance HadamardThreeLinesTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier HadamardThreeLinesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hadamardThreeLinesToEventFlow
  fromEventFlow := hadamardThreeLinesFromEventFlow

instance HadamardThreeLinesTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate HadamardThreeLinesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hadamardThreeLinesFromEventFlow (hadamardThreeLinesToEventFlow x) = some x
    exact HadamardThreeLinesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HadamardThreeLinesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance HadamardThreeLinesTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful HadamardThreeLinesUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hadamardThreeLinesFields
  field_faithful := HadamardThreeLinesTasteGate_single_carrier_alignment_fields_faithful

instance HadamardThreeLinesTasteGate_single_carrier_alignment_Nontrivial :
    BEDC.Meta.TasteGate.Nontrivial HadamardThreeLinesUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HadamardThreeLinesUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HadamardThreeLinesUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def HadamardThreeLinesTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate HadamardThreeLinesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  HadamardThreeLinesTasteGate_single_carrier_alignment_ChapterTasteGate

theorem HadamardThreeLinesTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HadamardThreeLinesUp) ∧
      Nonempty (FieldFaithful HadamardThreeLinesUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial HadamardThreeLinesUp) ∧
          (∀ h : BHist, hadamardThreeLinesDecodeBHist (hadamardThreeLinesEncodeBHist h) = h) ∧
            (∀ x : HadamardThreeLinesUp,
              hadamardThreeLinesFromEventFlow (hadamardThreeLinesToEventFlow x) = some x) ∧
              (∀ x y : HadamardThreeLinesUp,
                hadamardThreeLinesToEventFlow x = hadamardThreeLinesToEventFlow y → x = y) ∧
                hadamardThreeLinesEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨HadamardThreeLinesTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
      ⟨HadamardThreeLinesTasteGate_single_carrier_alignment_FieldFaithful⟩,
      ⟨HadamardThreeLinesTasteGate_single_carrier_alignment_Nontrivial⟩,
      HadamardThreeLinesTasteGate_single_carrier_alignment_decode_encode,
      HadamardThreeLinesTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact HadamardThreeLinesTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.HadamardThreeLinesUp
