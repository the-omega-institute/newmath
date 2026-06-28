import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArithmeticalHierarchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArithmeticalHierarchyUp : Type where
  | mk (S E Q B R L H C P N : BHist) : ArithmeticalHierarchyUp
  deriving DecidableEq

def arithmeticalHierarchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arithmeticalHierarchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arithmeticalHierarchyEncodeBHist h

def arithmeticalHierarchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arithmeticalHierarchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arithmeticalHierarchyDecodeBHist tail)

private theorem ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def arithmeticalHierarchyFields : ArithmeticalHierarchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArithmeticalHierarchyUp.mk S E Q B R L H C P N => [S, E, Q, B, R, L, H, C, P, N]

def arithmeticalHierarchyToEventFlow : ArithmeticalHierarchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (arithmeticalHierarchyFields x).map arithmeticalHierarchyEncodeBHist

private def ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt index rest

def arithmeticalHierarchyFromEventFlow (ef : EventFlow) : Option ArithmeticalHierarchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArithmeticalHierarchyUp.mk
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 0 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 1 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 2 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 3 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 4 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 5 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 6 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 7 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 8 ef))
      (arithmeticalHierarchyDecodeBHist
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem ArithmeticalHierarchyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArithmeticalHierarchyUp,
      arithmeticalHierarchyFromEventFlow (arithmeticalHierarchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S E Q B R L H C P N =>
      change
        some
          (ArithmeticalHierarchyUp.mk
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist S))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist E))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist Q))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist B))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist R))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist L))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist H))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist C))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist P))
            (arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist N))) =
          some (ArithmeticalHierarchyUp.mk S E Q B R L H C P N)
      rw [ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode S,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode E,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode Q,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode B,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode R,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode L,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode H,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode C,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode P,
        ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode N]

private theorem ArithmeticalHierarchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArithmeticalHierarchyUp} :
    arithmeticalHierarchyToEventFlow x = arithmeticalHierarchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arithmeticalHierarchyFromEventFlow (arithmeticalHierarchyToEventFlow x) =
        arithmeticalHierarchyFromEventFlow (arithmeticalHierarchyToEventFlow y) :=
    congrArg arithmeticalHierarchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ArithmeticalHierarchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArithmeticalHierarchyTasteGate_single_carrier_alignment_round_trip y)))

private theorem ArithmeticalHierarchyTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ArithmeticalHierarchyUp,
      arithmeticalHierarchyFields x = arithmeticalHierarchyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ E₁ Q₁ B₁ R₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ E₂ Q₂ B₂ R₂ L₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance arithmeticalHierarchyBHistCarrier : BHistCarrier ArithmeticalHierarchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arithmeticalHierarchyToEventFlow
  fromEventFlow := arithmeticalHierarchyFromEventFlow

instance arithmeticalHierarchyChapterTasteGate :
    ChapterTasteGate ArithmeticalHierarchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change arithmeticalHierarchyFromEventFlow (arithmeticalHierarchyToEventFlow x) = some x
    exact ArithmeticalHierarchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ArithmeticalHierarchyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance arithmeticalHierarchyFieldFaithful : FieldFaithful ArithmeticalHierarchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := arithmeticalHierarchyFields
  field_faithful := ArithmeticalHierarchyTasteGate_single_carrier_alignment_fields_faithful

instance arithmeticalHierarchyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ArithmeticalHierarchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArithmeticalHierarchyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ArithmeticalHierarchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ArithmeticalHierarchyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ArithmeticalHierarchyUp) ∧
      Nonempty (FieldFaithful ArithmeticalHierarchyUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ArithmeticalHierarchyUp) ∧
      (∀ h : BHist,
        arithmeticalHierarchyDecodeBHist (arithmeticalHierarchyEncodeBHist h) = h) ∧
      (∀ x : ArithmeticalHierarchyUp,
        arithmeticalHierarchyFromEventFlow (arithmeticalHierarchyToEventFlow x) = some x) ∧
      (∀ x y : ArithmeticalHierarchyUp,
        arithmeticalHierarchyToEventFlow x = arithmeticalHierarchyToEventFlow y → x = y) ∧
      arithmeticalHierarchyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact Nonempty.intro arithmeticalHierarchyChapterTasteGate
  · constructor
    · exact Nonempty.intro arithmeticalHierarchyFieldFaithful
    · constructor
      · exact Nonempty.intro arithmeticalHierarchyNontrivial
      · constructor
        · exact ArithmeticalHierarchyTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact ArithmeticalHierarchyTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact
                ArithmeticalHierarchyTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq
            · rfl

end BEDC.Derived.ArithmeticalHierarchyUp
