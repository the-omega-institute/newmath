import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalizationByEvaluationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalizationByEvaluationUp : Type where
  | mk (T G V NF R Ev H C P N : BHist) : NormalizationByEvaluationUp
  deriving DecidableEq

def normalizationByEvaluationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalizationByEvaluationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalizationByEvaluationEncodeBHist h

def normalizationByEvaluationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalizationByEvaluationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalizationByEvaluationDecodeBHist tail)

private theorem NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def normalizationByEvaluationFields : NormalizationByEvaluationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalizationByEvaluationUp.mk T G V NF R Ev H C P N => [T, G, V, NF, R, Ev, H, C, P, N]

def normalizationByEvaluationToEventFlow : NormalizationByEvaluationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (normalizationByEvaluationFields x).map normalizationByEvaluationEncodeBHist

private def normalizationByEvaluationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => normalizationByEvaluationEventAt index rest

def normalizationByEvaluationFromEventFlow
    (ef : EventFlow) : Option NormalizationByEvaluationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NormalizationByEvaluationUp.mk
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 0 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 1 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 2 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 3 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 4 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 5 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 6 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 7 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 8 ef))
      (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEventAt 9 ef)))

private theorem NormalizationByEvaluationTasteGate_single_carrier_alignment_round_trip
    (x : NormalizationByEvaluationUp) :
    normalizationByEvaluationFromEventFlow (normalizationByEvaluationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T G V NF R Ev H C P N =>
      change
        some
          (NormalizationByEvaluationUp.mk
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist T))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist G))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist V))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist NF))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist R))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist Ev))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist H))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist C))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist P))
            (normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist N))) =
          some (NormalizationByEvaluationUp.mk T G V NF R Ev H C P N)
      rw [NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode T,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode G,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode V,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode NF,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode R,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode Ev,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode H,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode C,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode P,
        NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode N]

private theorem NormalizationByEvaluationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NormalizationByEvaluationUp} :
    normalizationByEvaluationToEventFlow x = normalizationByEvaluationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalizationByEvaluationFromEventFlow (normalizationByEvaluationToEventFlow x) =
        normalizationByEvaluationFromEventFlow (normalizationByEvaluationToEventFlow y) :=
    congrArg normalizationByEvaluationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NormalizationByEvaluationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NormalizationByEvaluationTasteGate_single_carrier_alignment_round_trip y)))

private theorem NormalizationByEvaluationTasteGate_single_carrier_alignment_fields :
    ∀ x y : NormalizationByEvaluationUp,
      normalizationByEvaluationFields x = normalizationByEvaluationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ G₁ V₁ NF₁ R₁ Ev₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ G₂ V₂ NF₂ R₂ Ev₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance normalizationByEvaluationBHistCarrier : BHistCarrier NormalizationByEvaluationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalizationByEvaluationToEventFlow
  fromEventFlow := normalizationByEvaluationFromEventFlow

instance normalizationByEvaluationChapterTasteGate :
    ChapterTasteGate NormalizationByEvaluationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalizationByEvaluationFromEventFlow (normalizationByEvaluationToEventFlow x) =
      some x
    exact NormalizationByEvaluationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (NormalizationByEvaluationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance normalizationByEvaluationFieldFaithful :
    FieldFaithful NormalizationByEvaluationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := normalizationByEvaluationFields
  field_faithful := NormalizationByEvaluationTasteGate_single_carrier_alignment_fields

instance normalizationByEvaluationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial NormalizationByEvaluationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NormalizationByEvaluationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NormalizationByEvaluationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def NormalizationByEvaluationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate NormalizationByEvaluationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normalizationByEvaluationChapterTasteGate

theorem NormalizationByEvaluationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      normalizationByEvaluationDecodeBHist (normalizationByEvaluationEncodeBHist h) = h) ∧
      (forall x : NormalizationByEvaluationUp,
        normalizationByEvaluationFromEventFlow (normalizationByEvaluationToEventFlow x) =
          some x) ∧
        (forall x y : NormalizationByEvaluationUp,
          normalizationByEvaluationToEventFlow x = normalizationByEvaluationToEventFlow y ->
            x = y) ∧
          normalizationByEvaluationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact NormalizationByEvaluationTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact NormalizationByEvaluationTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact NormalizationByEvaluationTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.NormalizationByEvaluationUp
