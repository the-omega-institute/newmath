import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerRecognizerFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerRecognizerFlowUp : Type where
  | mk :
      (eventFlow sourceChannel generatedRecognizer certificateGate nonEvidence transport
        continuation provenance name : BHist) →
      GroundCompilerRecognizerFlowUp
  deriving DecidableEq

def groundCompilerRecognizerFlowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerRecognizerFlowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerRecognizerFlowEncodeBHist h

def groundCompilerRecognizerFlowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerRecognizerFlowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerRecognizerFlowDecodeBHist tail)

private theorem groundCompilerRecognizerFlow_decode_encode_bhist :
    ∀ h : BHist,
      groundCompilerRecognizerFlowDecodeBHist
        (groundCompilerRecognizerFlowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def groundCompilerRecognizerFlowFields : GroundCompilerRecognizerFlowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognizerFlowUp.mk eventFlow sourceChannel generatedRecognizer certificateGate
      nonEvidence transport continuation provenance name =>
      [eventFlow, sourceChannel, generatedRecognizer, certificateGate, nonEvidence, transport,
        continuation, provenance, name]

def groundCompilerRecognizerFlowToEventFlow : GroundCompilerRecognizerFlowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognizerFlowUp.mk eventFlow sourceChannel generatedRecognizer certificateGate
      nonEvidence transport continuation provenance name =>
      [[BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist eventFlow,
        [BMark.b1, BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist sourceChannel,
        [BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist generatedRecognizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist certificateGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist nonEvidence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        groundCompilerRecognizerFlowEncodeBHist name]

def groundCompilerRecognizerFlowFromEventFlow : EventFlow → Option GroundCompilerRecognizerFlowUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | eventFlow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sourceChannel :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | generatedRecognizer :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | certificateGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nonEvidence :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (GroundCompilerRecognizerFlowUp.mk
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    eventFlow)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    sourceChannel)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    generatedRecognizer)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    certificateGate)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    nonEvidence)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    transport)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    continuation)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    provenance)
                                                                                  (groundCompilerRecognizerFlowDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem groundCompilerRecognizerFlow_round_trip :
    ∀ x : GroundCompilerRecognizerFlowUp,
      groundCompilerRecognizerFlowFromEventFlow
        (groundCompilerRecognizerFlowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk eventFlow sourceChannel generatedRecognizer certificateGate nonEvidence transport
      continuation provenance name =>
      change
        some
          (GroundCompilerRecognizerFlowUp.mk
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist eventFlow))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist sourceChannel))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist generatedRecognizer))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist certificateGate))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist nonEvidence))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist transport))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist continuation))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist provenance))
            (groundCompilerRecognizerFlowDecodeBHist
              (groundCompilerRecognizerFlowEncodeBHist name))) =
          some
            (GroundCompilerRecognizerFlowUp.mk eventFlow sourceChannel generatedRecognizer
              certificateGate nonEvidence transport continuation provenance name)
      rw [groundCompilerRecognizerFlow_decode_encode_bhist eventFlow,
        groundCompilerRecognizerFlow_decode_encode_bhist sourceChannel,
        groundCompilerRecognizerFlow_decode_encode_bhist generatedRecognizer,
        groundCompilerRecognizerFlow_decode_encode_bhist certificateGate,
        groundCompilerRecognizerFlow_decode_encode_bhist nonEvidence,
        groundCompilerRecognizerFlow_decode_encode_bhist transport,
        groundCompilerRecognizerFlow_decode_encode_bhist continuation,
        groundCompilerRecognizerFlow_decode_encode_bhist provenance,
        groundCompilerRecognizerFlow_decode_encode_bhist name]

private theorem groundCompilerRecognizerFlowToEventFlow_injective
    {x y : GroundCompilerRecognizerFlowUp} :
    groundCompilerRecognizerFlowToEventFlow x =
      groundCompilerRecognizerFlowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerRecognizerFlowFromEventFlow
          (groundCompilerRecognizerFlowToEventFlow x) =
        groundCompilerRecognizerFlowFromEventFlow
          (groundCompilerRecognizerFlowToEventFlow y) :=
    congrArg groundCompilerRecognizerFlowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerRecognizerFlow_round_trip x).symm
      (Eq.trans hread (groundCompilerRecognizerFlow_round_trip y)))

private theorem groundCompilerRecognizerFlow_field_faithful :
    ∀ x y : GroundCompilerRecognizerFlowUp,
      groundCompilerRecognizerFlowFields x = groundCompilerRecognizerFlowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk eventFlow sourceChannel generatedRecognizer certificateGate nonEvidence transport
      continuation provenance name =>
      cases y with
      | mk eventFlow' sourceChannel' generatedRecognizer' certificateGate' nonEvidence'
          transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance groundCompilerRecognizerFlowBHistCarrier :
    BHistCarrier GroundCompilerRecognizerFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerRecognizerFlowToEventFlow
  fromEventFlow := groundCompilerRecognizerFlowFromEventFlow

instance groundCompilerRecognizerFlowChapterTasteGate :
    ChapterTasteGate GroundCompilerRecognizerFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerRecognizerFlowFromEventFlow (groundCompilerRecognizerFlowToEventFlow x) =
        some x
    exact groundCompilerRecognizerFlow_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerRecognizerFlowToEventFlow_injective heq)

instance groundCompilerRecognizerFlowFieldFaithful :
    FieldFaithful GroundCompilerRecognizerFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := groundCompilerRecognizerFlowFields
  field_faithful := groundCompilerRecognizerFlow_field_faithful

instance groundCompilerRecognizerFlowNontrivial : Nontrivial GroundCompilerRecognizerFlowUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GroundCompilerRecognizerFlowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GroundCompilerRecognizerFlowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GroundCompilerRecognizerFlowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  groundCompilerRecognizerFlowChapterTasteGate

theorem GroundCompilerRecognizerFlowTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      groundCompilerRecognizerFlowDecodeBHist
        (groundCompilerRecognizerFlowEncodeBHist h) = h) ∧
      (∀ x : GroundCompilerRecognizerFlowUp,
        groundCompilerRecognizerFlowFromEventFlow
          (groundCompilerRecognizerFlowToEventFlow x) = some x) ∧
        (∀ x y : GroundCompilerRecognizerFlowUp,
          groundCompilerRecognizerFlowToEventFlow x =
            groundCompilerRecognizerFlowToEventFlow y → x = y) ∧
          groundCompilerRecognizerFlowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundCompilerRecognizerFlow_decode_encode_bhist
  · constructor
    · exact groundCompilerRecognizerFlow_round_trip
    · constructor
      · intro x y heq
        exact groundCompilerRecognizerFlowToEventFlow_injective heq
      · rfl

end BEDC.Derived.GroundCompilerRecognizerFlowUp
