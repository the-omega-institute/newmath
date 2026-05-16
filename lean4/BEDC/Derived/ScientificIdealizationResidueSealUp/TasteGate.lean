import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ScientificIdealizationResidueSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ScientificIdealizationResidueSealUp : Type where
  | mk :
      (explanation methodology residue boundary audit idealization residueLedger descent failure
        scope transport continuation provenance name : BHist) →
      ScientificIdealizationResidueSealUp
  deriving DecidableEq

def scientificIdealizationResidueSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: scientificIdealizationResidueSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: scientificIdealizationResidueSealEncodeBHist h

def scientificIdealizationResidueSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (scientificIdealizationResidueSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (scientificIdealizationResidueSealDecodeBHist tail)

private theorem scientificIdealizationResidueSeal_decode_encode_bhist :
    ∀ h : BHist,
      scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def scientificIdealizationResidueSealFields :
    ScientificIdealizationResidueSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ScientificIdealizationResidueSealUp.mk explanation methodology residue boundary audit
      idealization residueLedger descent failure scope transport continuation provenance name =>
      [explanation, methodology, residue, boundary, audit, idealization, residueLedger,
        descent, failure, scope, transport, continuation, provenance, name]

def scientificIdealizationResidueSealToEventFlow :
    ScientificIdealizationResidueSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ScientificIdealizationResidueSealUp.mk explanation methodology residue boundary audit
      idealization residueLedger descent failure scope transport continuation provenance name =>
      [[BMark.b0],
        scientificIdealizationResidueSealEncodeBHist explanation,
        [BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist methodology,
        [BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist idealization,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist residueLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        scientificIdealizationResidueSealEncodeBHist descent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist scope,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        scientificIdealizationResidueSealEncodeBHist name]

private def scientificIdealizationResidueSealEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      scientificIdealizationResidueSealEventAtDefault index rest

def scientificIdealizationResidueSealFromEventFlow
    (ef : EventFlow) : Option ScientificIdealizationResidueSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ScientificIdealizationResidueSealUp.mk
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 1 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 3 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 5 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 7 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 9 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 11 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 13 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 15 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 17 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 19 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 21 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 23 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 25 ef))
      (scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEventAtDefault 27 ef)))

private theorem scientificIdealizationResidueSeal_round_trip :
    ∀ x : ScientificIdealizationResidueSealUp,
      scientificIdealizationResidueSealFromEventFlow
        (scientificIdealizationResidueSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk explanation methodology residue boundary audit idealization residueLedger descent
      failure scope transport continuation provenance name =>
      change
        some
          (ScientificIdealizationResidueSealUp.mk
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist explanation))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist methodology))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist residue))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist boundary))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist audit))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist idealization))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist residueLedger))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist descent))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist failure))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist scope))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist transport))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist continuation))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist provenance))
            (scientificIdealizationResidueSealDecodeBHist
              (scientificIdealizationResidueSealEncodeBHist name))) =
          some
            (ScientificIdealizationResidueSealUp.mk explanation methodology residue boundary
              audit idealization residueLedger descent failure scope transport continuation
              provenance name)
      rw [scientificIdealizationResidueSeal_decode_encode_bhist explanation,
        scientificIdealizationResidueSeal_decode_encode_bhist methodology,
        scientificIdealizationResidueSeal_decode_encode_bhist residue,
        scientificIdealizationResidueSeal_decode_encode_bhist boundary,
        scientificIdealizationResidueSeal_decode_encode_bhist audit,
        scientificIdealizationResidueSeal_decode_encode_bhist idealization,
        scientificIdealizationResidueSeal_decode_encode_bhist residueLedger,
        scientificIdealizationResidueSeal_decode_encode_bhist descent,
        scientificIdealizationResidueSeal_decode_encode_bhist failure,
        scientificIdealizationResidueSeal_decode_encode_bhist scope,
        scientificIdealizationResidueSeal_decode_encode_bhist transport,
        scientificIdealizationResidueSeal_decode_encode_bhist continuation,
        scientificIdealizationResidueSeal_decode_encode_bhist provenance,
        scientificIdealizationResidueSeal_decode_encode_bhist name]

private theorem scientificIdealizationResidueSealToEventFlow_injective
    {x y : ScientificIdealizationResidueSealUp} :
    scientificIdealizationResidueSealToEventFlow x =
      scientificIdealizationResidueSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      scientificIdealizationResidueSealFromEventFlow
          (scientificIdealizationResidueSealToEventFlow x) =
        scientificIdealizationResidueSealFromEventFlow
          (scientificIdealizationResidueSealToEventFlow y) :=
    congrArg scientificIdealizationResidueSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (scientificIdealizationResidueSeal_round_trip x).symm
      (Eq.trans hread (scientificIdealizationResidueSeal_round_trip y)))

private theorem scientificIdealizationResidueSeal_field_faithful :
    ∀ x y : ScientificIdealizationResidueSealUp,
      scientificIdealizationResidueSealFields x =
        scientificIdealizationResidueSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk explanation₁ methodology₁ residue₁ boundary₁ audit₁ idealization₁ residueLedger₁
      descent₁ failure₁ scope₁ transport₁ continuation₁ provenance₁ name₁ =>
      cases y with
      | mk explanation₂ methodology₂ residue₂ boundary₂ audit₂ idealization₂ residueLedger₂
          descent₂ failure₂ scope₂ transport₂ continuation₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance scientificIdealizationResidueSealBHistCarrier :
    BHistCarrier ScientificIdealizationResidueSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := scientificIdealizationResidueSealToEventFlow
  fromEventFlow := scientificIdealizationResidueSealFromEventFlow

instance scientificIdealizationResidueSealChapterTasteGate :
    ChapterTasteGate ScientificIdealizationResidueSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change scientificIdealizationResidueSealFromEventFlow
      (scientificIdealizationResidueSealToEventFlow x) = some x
    exact scientificIdealizationResidueSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (scientificIdealizationResidueSealToEventFlow_injective heq)

instance scientificIdealizationResidueSealFieldFaithful :
    FieldFaithful ScientificIdealizationResidueSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := scientificIdealizationResidueSealFields
  field_faithful := scientificIdealizationResidueSeal_field_faithful

instance scientificIdealizationResidueSealNontrivial :
    Nontrivial ScientificIdealizationResidueSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ScientificIdealizationResidueSealUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ScientificIdealizationResidueSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ScientificIdealizationResidueSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  scientificIdealizationResidueSealChapterTasteGate

theorem ScientificIdealizationResidueSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      scientificIdealizationResidueSealDecodeBHist
        (scientificIdealizationResidueSealEncodeBHist h) = h) ∧
      (∀ x : ScientificIdealizationResidueSealUp,
        scientificIdealizationResidueSealFromEventFlow
          (scientificIdealizationResidueSealToEventFlow x) = some x) ∧
        scientificIdealizationResidueSealEncodeBHist BHist.Empty = ([] : List BMark) ∧
          Nonempty (ChapterTasteGate ScientificIdealizationResidueSealUp) ∧
            Nonempty (BHistCarrier ScientificIdealizationResidueSealUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact scientificIdealizationResidueSeal_decode_encode_bhist
  · constructor
    · exact scientificIdealizationResidueSeal_round_trip
    · constructor
      · rfl
      · constructor
        · exact ⟨scientificIdealizationResidueSealChapterTasteGate⟩
        · exact ⟨scientificIdealizationResidueSealBHistCarrier⟩

end BEDC.Derived.ScientificIdealizationResidueSealUp
