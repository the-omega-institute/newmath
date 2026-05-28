import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CandidateSetNormalizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CandidateSetNormalizationUp : Type where
  | mk :
      (candidate closedTerm adequacy noInfinite obstruction transport replay provenance
        localName : BHist) →
        CandidateSetNormalizationUp
  deriving DecidableEq

def candidateSetNormalizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: candidateSetNormalizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: candidateSetNormalizationEncodeBHist h

def candidateSetNormalizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (candidateSetNormalizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (candidateSetNormalizationDecodeBHist tail)

private theorem candidateSetNormalization_decode_encode_bhist :
    ∀ h : BHist, candidateSetNormalizationDecodeBHist
      (candidateSetNormalizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def candidateSetNormalizationFields : CandidateSetNormalizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CandidateSetNormalizationUp.mk candidate closedTerm adequacy noInfinite obstruction
      transport replay provenance localName =>
      [candidate, closedTerm, adequacy, noInfinite, obstruction, transport, replay, provenance,
        localName]

def candidateSetNormalizationToEventFlow : CandidateSetNormalizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (candidateSetNormalizationFields x).map candidateSetNormalizationEncodeBHist

def candidateSetNormalizationFromEventFlow : EventFlow → Option CandidateSetNormalizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | candidate :: closedTerm :: adequacy :: noInfinite :: obstruction :: transport :: replay ::
      provenance :: localName :: [] =>
      some
        (CandidateSetNormalizationUp.mk
          (candidateSetNormalizationDecodeBHist candidate)
          (candidateSetNormalizationDecodeBHist closedTerm)
          (candidateSetNormalizationDecodeBHist adequacy)
          (candidateSetNormalizationDecodeBHist noInfinite)
          (candidateSetNormalizationDecodeBHist obstruction)
          (candidateSetNormalizationDecodeBHist transport)
          (candidateSetNormalizationDecodeBHist replay)
          (candidateSetNormalizationDecodeBHist provenance)
          (candidateSetNormalizationDecodeBHist localName))
  | _ => none

private theorem candidateSetNormalization_round_trip :
    ∀ x : CandidateSetNormalizationUp,
      candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate closedTerm adequacy noInfinite obstruction transport replay provenance
      localName =>
      change
        some
          (CandidateSetNormalizationUp.mk
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist candidate))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist closedTerm))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist adequacy))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist noInfinite))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist obstruction))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist transport))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist replay))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist provenance))
            (candidateSetNormalizationDecodeBHist
              (candidateSetNormalizationEncodeBHist localName))) =
          some
            (CandidateSetNormalizationUp.mk candidate closedTerm adequacy noInfinite obstruction
              transport replay provenance localName)
      rw [candidateSetNormalization_decode_encode_bhist candidate,
        candidateSetNormalization_decode_encode_bhist closedTerm,
        candidateSetNormalization_decode_encode_bhist adequacy,
        candidateSetNormalization_decode_encode_bhist noInfinite,
        candidateSetNormalization_decode_encode_bhist obstruction,
        candidateSetNormalization_decode_encode_bhist transport,
        candidateSetNormalization_decode_encode_bhist replay,
        candidateSetNormalization_decode_encode_bhist provenance,
        candidateSetNormalization_decode_encode_bhist localName]

private theorem candidateSetNormalizationToEventFlow_injective
    {x y : CandidateSetNormalizationUp} :
    candidateSetNormalizationToEventFlow x = candidateSetNormalizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow x) =
        candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow y) :=
    congrArg candidateSetNormalizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (candidateSetNormalization_round_trip x).symm
      (Eq.trans hread (candidateSetNormalization_round_trip y)))

private theorem candidateSetNormalization_fields_faithful :
    ∀ x y : CandidateSetNormalizationUp,
      candidateSetNormalizationFields x = candidateSetNormalizationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk candidate₁ closedTerm₁ adequacy₁ noInfinite₁ obstruction₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk candidate₂ closedTerm₂ adequacy₂ noInfinite₂ obstruction₂ transport₂ replay₂
          provenance₂ localName₂ =>
          injection hfields with hCandidate tail0
          injection tail0 with hClosedTerm tail1
          injection tail1 with hAdequacy tail2
          injection tail2 with hNoInfinite tail3
          injection tail3 with hObstruction tail4
          injection tail4 with hTransport tail5
          injection tail5 with hReplay tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hLocalName _
          subst hCandidate
          subst hClosedTerm
          subst hAdequacy
          subst hNoInfinite
          subst hObstruction
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance candidateSetNormalizationBHistCarrier :
    BHistCarrier CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := candidateSetNormalizationToEventFlow
  fromEventFlow := candidateSetNormalizationFromEventFlow

instance candidateSetNormalizationChapterTasteGate :
    ChapterTasteGate CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change candidateSetNormalizationFromEventFlow (candidateSetNormalizationToEventFlow x) =
      some x
    exact candidateSetNormalization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (candidateSetNormalizationToEventFlow_injective heq)

instance candidateSetNormalizationFieldFaithful :
    FieldFaithful CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := candidateSetNormalizationFields
  field_faithful := candidateSetNormalization_fields_faithful

instance candidateSetNormalizationNontrivial : Nontrivial CandidateSetNormalizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CandidateSetNormalizationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CandidateSetNormalizationUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CandidateSetNormalizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  candidateSetNormalizationChapterTasteGate

end BEDC.Derived.CandidateSetNormalizationUp
