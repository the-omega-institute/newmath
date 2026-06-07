import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NaturalDeductionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NaturalDeductionUp : Type where
  | mk :
      (assumption rule discharge conclusion boundary transport component replay provenance
        name : BHist) →
        NaturalDeductionUp
  deriving DecidableEq

def naturalDeductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: naturalDeductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: naturalDeductionEncodeBHist h

def naturalDeductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (naturalDeductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (naturalDeductionDecodeBHist tail)

private def naturalDeductionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => naturalDeductionRawAt n rest

private theorem naturalDeduction_decode_encode_bhist :
    ∀ h : BHist, naturalDeductionDecodeBHist (naturalDeductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def naturalDeductionFields : NaturalDeductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NaturalDeductionUp.mk assumption rule discharge conclusion boundary transport component replay
      provenance name =>
      [assumption, rule, discharge, conclusion, boundary, transport, component, replay,
        provenance, name]

def naturalDeductionToEventFlow : NaturalDeductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NaturalDeductionUp.mk assumption rule discharge conclusion boundary transport component replay
      provenance name =>
      [naturalDeductionEncodeBHist assumption,
        naturalDeductionEncodeBHist rule,
        naturalDeductionEncodeBHist discharge,
        naturalDeductionEncodeBHist conclusion,
        naturalDeductionEncodeBHist boundary,
        naturalDeductionEncodeBHist transport,
        naturalDeductionEncodeBHist component,
        naturalDeductionEncodeBHist replay,
        naturalDeductionEncodeBHist provenance,
        naturalDeductionEncodeBHist name]

def naturalDeductionFromEventFlow (ef : EventFlow) : Option NaturalDeductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NaturalDeductionUp.mk
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 0 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 1 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 2 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 3 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 4 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 5 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 6 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 7 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 8 ef))
      (naturalDeductionDecodeBHist (naturalDeductionRawAt 9 ef)))

private theorem naturalDeduction_round_trip :
    ∀ x : NaturalDeductionUp,
      naturalDeductionFromEventFlow (naturalDeductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk assumption rule discharge conclusion boundary transport component replay provenance name =>
      change
        some
          (NaturalDeductionUp.mk
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist assumption))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist rule))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist discharge))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist conclusion))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist boundary))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist transport))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist component))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist replay))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist provenance))
            (naturalDeductionDecodeBHist (naturalDeductionEncodeBHist name))) =
          some
            (NaturalDeductionUp.mk assumption rule discharge conclusion boundary transport
              component replay provenance name)
      rw [naturalDeduction_decode_encode_bhist assumption,
        naturalDeduction_decode_encode_bhist rule,
        naturalDeduction_decode_encode_bhist discharge,
        naturalDeduction_decode_encode_bhist conclusion,
        naturalDeduction_decode_encode_bhist boundary,
        naturalDeduction_decode_encode_bhist transport,
        naturalDeduction_decode_encode_bhist component,
        naturalDeduction_decode_encode_bhist replay,
        naturalDeduction_decode_encode_bhist provenance,
        naturalDeduction_decode_encode_bhist name]

private theorem naturalDeductionToEventFlow_injective {x y : NaturalDeductionUp} :
    naturalDeductionToEventFlow x = naturalDeductionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      naturalDeductionFromEventFlow (naturalDeductionToEventFlow x) =
        naturalDeductionFromEventFlow (naturalDeductionToEventFlow y) :=
    congrArg naturalDeductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (naturalDeduction_round_trip x).symm
      (Eq.trans hread (naturalDeduction_round_trip y)))

private theorem naturalDeduction_field_faithful :
    ∀ x y : NaturalDeductionUp, naturalDeductionFields x = naturalDeductionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk assumption rule discharge conclusion boundary transport component replay provenance name =>
      cases y with
      | mk assumption' rule' discharge' conclusion' boundary' transport' component' replay'
          provenance' name' =>
          cases hfields
          rfl

instance naturalDeductionBHistCarrier : BHistCarrier NaturalDeductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := naturalDeductionToEventFlow
  fromEventFlow := naturalDeductionFromEventFlow

instance naturalDeductionChapterTasteGate : ChapterTasteGate NaturalDeductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change naturalDeductionFromEventFlow (naturalDeductionToEventFlow x) = some x
    exact naturalDeduction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (naturalDeductionToEventFlow_injective heq)

instance naturalDeductionFieldFaithful : FieldFaithful NaturalDeductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := naturalDeductionFields
  field_faithful := naturalDeduction_field_faithful

instance naturalDeductionNontrivial : Nontrivial NaturalDeductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NaturalDeductionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NaturalDeductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NaturalDeductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  naturalDeductionChapterTasteGate

theorem NaturalDeductionTasteGate_single_carrier_alignment :
    (∀ h : BHist, naturalDeductionDecodeBHist (naturalDeductionEncodeBHist h) = h) ∧
      Nonempty (Nontrivial NaturalDeductionUp) ∧
        Nonempty (ChapterTasteGate NaturalDeductionUp) ∧
          Nonempty (FieldFaithful NaturalDeductionUp) ∧
            naturalDeductionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨naturalDeduction_decode_encode_bhist,
      ⟨⟨naturalDeductionNontrivial⟩,
        ⟨⟨naturalDeductionChapterTasteGate⟩,
          ⟨⟨naturalDeductionFieldFaithful⟩, rfl⟩⟩⟩⟩

end BEDC.Derived.NaturalDeductionUp.TasteGate
