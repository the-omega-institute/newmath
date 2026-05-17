import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RecursorBranchCompletenessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RecursorBranchCompletenessUp : Type where
  | mk :
      (signature recursor motive branches completeness transport replay provenance name : BHist) →
      RecursorBranchCompletenessUp
  deriving DecidableEq

def recursorBranchCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: recursorBranchCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: recursorBranchCompletenessEncodeBHist h

def recursorBranchCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (recursorBranchCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (recursorBranchCompletenessDecodeBHist tail)

private theorem recursorBranchCompleteness_decode_encode_bhist :
    ∀ h : BHist,
      recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def recursorBranchCompletenessFields : RecursorBranchCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RecursorBranchCompletenessUp.mk signature recursor motive branches completeness
      transport replay provenance name =>
      [signature, recursor, motive, branches, completeness, transport, replay, provenance, name]

def recursorBranchCompletenessToEventFlow : RecursorBranchCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (recursorBranchCompletenessFields x).map recursorBranchCompletenessEncodeBHist

private def recursorBranchCompletenessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => recursorBranchCompletenessEventAtDefault index rest

def recursorBranchCompletenessFromEventFlow
    (ef : EventFlow) : Option RecursorBranchCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RecursorBranchCompletenessUp.mk
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 0 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 1 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 2 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 3 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 4 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 5 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 6 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 7 ef))
      (recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEventAtDefault 8 ef)))

private theorem recursorBranchCompleteness_round_trip :
    ∀ x : RecursorBranchCompletenessUp,
      recursorBranchCompletenessFromEventFlow
        (recursorBranchCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk signature recursor motive branches completeness transport replay provenance name =>
      change
        some
          (RecursorBranchCompletenessUp.mk
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist signature))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist recursor))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist motive))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist branches))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist completeness))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist transport))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist replay))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist provenance))
            (recursorBranchCompletenessDecodeBHist
              (recursorBranchCompletenessEncodeBHist name))) =
          some
            (RecursorBranchCompletenessUp.mk signature recursor motive branches completeness
              transport replay provenance name)
      rw [recursorBranchCompleteness_decode_encode_bhist signature,
        recursorBranchCompleteness_decode_encode_bhist recursor,
        recursorBranchCompleteness_decode_encode_bhist motive,
        recursorBranchCompleteness_decode_encode_bhist branches,
        recursorBranchCompleteness_decode_encode_bhist completeness,
        recursorBranchCompleteness_decode_encode_bhist transport,
        recursorBranchCompleteness_decode_encode_bhist replay,
        recursorBranchCompleteness_decode_encode_bhist provenance,
        recursorBranchCompleteness_decode_encode_bhist name]

private theorem recursorBranchCompletenessToEventFlow_injective
    {x y : RecursorBranchCompletenessUp} :
    recursorBranchCompletenessToEventFlow x = recursorBranchCompletenessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      recursorBranchCompletenessFromEventFlow (recursorBranchCompletenessToEventFlow x) =
        recursorBranchCompletenessFromEventFlow (recursorBranchCompletenessToEventFlow y) :=
    congrArg recursorBranchCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (recursorBranchCompleteness_round_trip x).symm
      (Eq.trans hread (recursorBranchCompleteness_round_trip y)))

private theorem recursorBranchCompleteness_fields_faithful :
    ∀ x y : RecursorBranchCompletenessUp,
      recursorBranchCompletenessFields x = recursorBranchCompletenessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk i₁ r₁ m₁ b₁ k₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk i₂ r₂ m₂ b₂ k₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance recursorBranchCompletenessBHistCarrier :
    BHistCarrier RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := recursorBranchCompletenessToEventFlow
  fromEventFlow := recursorBranchCompletenessFromEventFlow

instance recursorBranchCompletenessChapterTasteGate :
    ChapterTasteGate RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      recursorBranchCompletenessFromEventFlow (recursorBranchCompletenessToEventFlow x) =
        some x
    exact recursorBranchCompleteness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (recursorBranchCompletenessToEventFlow_injective heq)

instance recursorBranchCompletenessFieldFaithful :
    FieldFaithful RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := recursorBranchCompletenessFields
  field_faithful := recursorBranchCompleteness_fields_faithful

instance recursorBranchCompletenessNontrivial : Nontrivial RecursorBranchCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RecursorBranchCompletenessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RecursorBranchCompletenessUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RecursorBranchCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  recursorBranchCompletenessChapterTasteGate

def taste_gate_witness : FieldFaithful RecursorBranchCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  recursorBranchCompletenessFieldFaithful

theorem RecursorBranchCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      recursorBranchCompletenessDecodeBHist
        (recursorBranchCompletenessEncodeBHist h) = h) ∧
      (∀ x : RecursorBranchCompletenessUp,
        recursorBranchCompletenessFromEventFlow
          (recursorBranchCompletenessToEventFlow x) = some x) ∧
        Nonempty (ChapterTasteGate RecursorBranchCompletenessUp) ∧
          recursorBranchCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨recursorBranchCompleteness_decode_encode_bhist,
      recursorBranchCompleteness_round_trip,
      ⟨recursorBranchCompletenessChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RecursorBranchCompletenessUp.TasteGate
