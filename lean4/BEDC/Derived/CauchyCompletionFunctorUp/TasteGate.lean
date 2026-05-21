import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionFunctorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionFunctorUp : Type where
  | mk :
      (metricRow regularRow sealRow monadRow universalRow classifierRow transportRow nameCertRow endpointRow : BHist) ->
        CauchyCompletionFunctorUp
  deriving DecidableEq

def cauchyCompletionFunctorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionFunctorEncodeBHist h

def cauchyCompletionFunctorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionFunctorDecodeBHist tail)

theorem CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyCompletionFunctorFields : CauchyCompletionFunctorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionFunctorUp.mk metricRow regularRow sealRow monadRow universalRow classifierRow transportRow
      nameCertRow endpointRow =>
      [metricRow, regularRow, sealRow, monadRow, universalRow, classifierRow, transportRow, nameCertRow, endpointRow]

def cauchyCompletionFunctorToEventFlow : CauchyCompletionFunctorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionFunctorUp.mk metricRow regularRow sealRow monadRow universalRow
      classifierRow transportRow nameCertRow endpointRow =>
      [[BMark.b0],
        cauchyCompletionFunctorEncodeBHist metricRow,
        [BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist regularRow,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist monadRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist universalRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist classifierRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist transportRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyCompletionFunctorEncodeBHist nameCertRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyCompletionFunctorEncodeBHist endpointRow]

def cauchyCompletionFunctorFromEventFlow : EventFlow -> Option CauchyCompletionFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metricRow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | regularRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sealRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | monadRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | universalRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | classifierRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transportRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCertRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | endpointRow :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (CauchyCompletionFunctorUp.mk
                                                                                  (cauchyCompletionFunctorDecodeBHist metricRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist regularRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist sealRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist monadRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist universalRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist classifierRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist transportRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist nameCertRow)
                                                                                  (cauchyCompletionFunctorDecodeBHist endpointRow))
                                                                          | _ :: _ => none

theorem CauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyCompletionFunctorUp,
      cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricRow regularRow sealRow monadRow universalRow classifierRow transportRow nameCertRow endpointRow =>
      change
        some
          (CauchyCompletionFunctorUp.mk
            (cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist metricRow))
            (cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist regularRow))
            (cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist sealRow))
            (cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist monadRow))
            (cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist universalRow))
            (cauchyCompletionFunctorDecodeBHist
              (cauchyCompletionFunctorEncodeBHist classifierRow))
            (cauchyCompletionFunctorDecodeBHist
              (cauchyCompletionFunctorEncodeBHist transportRow))
            (cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist nameCertRow))
            (cauchyCompletionFunctorDecodeBHist
              (cauchyCompletionFunctorEncodeBHist endpointRow))) =
          some
            (CauchyCompletionFunctorUp.mk metricRow regularRow sealRow monadRow universalRow classifierRow
              transportRow nameCertRow endpointRow)
      rw [CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode metricRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode regularRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode sealRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode monadRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode universalRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode classifierRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode transportRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode nameCertRow,
        CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode endpointRow]

theorem CauchyCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionFunctorUp} :
    cauchyCompletionFunctorToEventFlow x = cauchyCompletionFunctorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow x) =
        cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow y) :=
    congrArg cauchyCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

theorem CauchyCompletionFunctorTasteGate_single_carrier_alignment_field_faithful :
    forall x y : CauchyCompletionFunctorUp,
      cauchyCompletionFunctorFields x = cauchyCompletionFunctorFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metricRow₁ regularRow₁ sealRow₁ monadRow₁ universalRow₁ classifierRow₁ transportRow₁ nameCertRow₁ endpointRow₁ =>
      cases y with
      | mk metricRow₂ regularRow₂ sealRow₂ monadRow₂ universalRow₂ classifierRow₂ transportRow₂ nameCertRow₂
          endpointRow₂ =>
          cases hfields
          rfl

instance cauchyCompletionFunctorBHistCarrier : BHistCarrier CauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionFunctorToEventFlow
  fromEventFlow := cauchyCompletionFunctorFromEventFlow

instance cauchyCompletionFunctorChapterTasteGate :
    ChapterTasteGate CauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (CauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyCompletionFunctorFieldFaithful : FieldFaithful CauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionFunctorFields
  field_faithful := CauchyCompletionFunctorTasteGate_single_carrier_alignment_field_faithful

instance cauchyCompletionFunctorNontrivial : Nontrivial CauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionFunctorChapterTasteGate

theorem CauchyCompletionFunctorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionFunctorUp) ∧
      Nonempty (FieldFaithful CauchyCompletionFunctorUp) ∧
        Nonempty (Nontrivial CauchyCompletionFunctorUp) ∧
          (∀ h : BHist,
            cauchyCompletionFunctorDecodeBHist (cauchyCompletionFunctorEncodeBHist h) = h) ∧
            (∀ x : CauchyCompletionFunctorUp,
              cauchyCompletionFunctorFromEventFlow (cauchyCompletionFunctorToEventFlow x) =
                some x) ∧
              (∀ x y : CauchyCompletionFunctorUp,
                cauchyCompletionFunctorToEventFlow x = cauchyCompletionFunctorToEventFlow y ->
                  x = y) ∧
                cauchyCompletionFunctorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyCompletionFunctorChapterTasteGate⟩
  · constructor
    · exact ⟨cauchyCompletionFunctorFieldFaithful⟩
    · constructor
      · exact ⟨cauchyCompletionFunctorNontrivial⟩
      · constructor
        · exact CauchyCompletionFunctorTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact CauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact CauchyCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.CauchyCompletionFunctorUp.TasteGate
