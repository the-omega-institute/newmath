import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TasteGateAdmissionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TasteGateAdmissionUp : Type where
  | mk :
      (chapter origin nameCert tasteGate eventFlow compilerRefs transport routes provenance
        refusal : BHist) →
      TasteGateAdmissionUp
  deriving DecidableEq

def tasteGateAdmissionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tasteGateAdmissionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tasteGateAdmissionEncodeBHist h

def tasteGateAdmissionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tasteGateAdmissionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tasteGateAdmissionDecodeBHist tail)

private theorem tasteGateAdmissionDecode_encode_bhist :
    ∀ h : BHist, tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tasteGateAdmissionToEventFlow : TasteGateAdmissionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TasteGateAdmissionUp.mk chapter origin nameCert tasteGate eventFlow compilerRefs transport
      routes provenance refusal =>
      [[BMark.b0],
        tasteGateAdmissionEncodeBHist chapter,
        [BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist origin,
        [BMark.b1, BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist nameCert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist tasteGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist eventFlow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist compilerRefs,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tasteGateAdmissionEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        tasteGateAdmissionEncodeBHist refusal]

def tasteGateAdmissionFromEventFlow : EventFlow → Option TasteGateAdmissionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | chapter :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | origin :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | nameCert :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tasteGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | eventFlow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | compilerRefs :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | routes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | refusal ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (TasteGateAdmissionUp.mk
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            chapter)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            origin)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            nameCert)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            tasteGate)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            eventFlow)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            compilerRefs)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            transport)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            routes)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            provenance)
                                                                                          (tasteGateAdmissionDecodeBHist
                                                                                            refusal))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem tasteGateAdmission_round_trip :
    ∀ x : TasteGateAdmissionUp,
      tasteGateAdmissionFromEventFlow (tasteGateAdmissionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk chapter origin nameCert tasteGate eventFlow compilerRefs transport routes provenance
      refusal =>
      change
        some
          (TasteGateAdmissionUp.mk
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist chapter))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist origin))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist nameCert))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist tasteGate))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist eventFlow))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist compilerRefs))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist transport))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist routes))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist provenance))
            (tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist refusal))) =
          some
            (TasteGateAdmissionUp.mk chapter origin nameCert tasteGate eventFlow compilerRefs
              transport routes provenance refusal)
      rw [tasteGateAdmissionDecode_encode_bhist chapter,
        tasteGateAdmissionDecode_encode_bhist origin,
        tasteGateAdmissionDecode_encode_bhist nameCert,
        tasteGateAdmissionDecode_encode_bhist tasteGate,
        tasteGateAdmissionDecode_encode_bhist eventFlow,
        tasteGateAdmissionDecode_encode_bhist compilerRefs,
        tasteGateAdmissionDecode_encode_bhist transport,
        tasteGateAdmissionDecode_encode_bhist routes,
        tasteGateAdmissionDecode_encode_bhist provenance,
        tasteGateAdmissionDecode_encode_bhist refusal]

private theorem tasteGateAdmissionToEventFlow_injective {x y : TasteGateAdmissionUp} :
    tasteGateAdmissionToEventFlow x = tasteGateAdmissionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tasteGateAdmissionFromEventFlow (tasteGateAdmissionToEventFlow x) =
        tasteGateAdmissionFromEventFlow (tasteGateAdmissionToEventFlow y) :=
    congrArg tasteGateAdmissionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tasteGateAdmission_round_trip x).symm
      (Eq.trans hread (tasteGateAdmission_round_trip y)))

instance tasteGateAdmissionBHistCarrier : BHistCarrier TasteGateAdmissionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tasteGateAdmissionToEventFlow
  fromEventFlow := tasteGateAdmissionFromEventFlow

instance tasteGateAdmissionChapterTasteGate : ChapterTasteGate TasteGateAdmissionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tasteGateAdmissionFromEventFlow (tasteGateAdmissionToEventFlow x) = some x
    exact tasteGateAdmission_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tasteGateAdmissionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TasteGateAdmissionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tasteGateAdmissionChapterTasteGate

theorem TasteGateAdmissionTasteGate_single_carrier_alignment :
    (∀ h : BHist, tasteGateAdmissionDecodeBHist (tasteGateAdmissionEncodeBHist h) = h) ∧
      (∀ x : TasteGateAdmissionUp,
        tasteGateAdmissionFromEventFlow (tasteGateAdmissionToEventFlow x) = some x) ∧
        (∀ x y : TasteGateAdmissionUp,
          tasteGateAdmissionToEventFlow x = tasteGateAdmissionToEventFlow y → x = y) ∧
          tasteGateAdmissionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact tasteGateAdmissionDecode_encode_bhist
  · constructor
    · exact tasteGateAdmission_round_trip
    · constructor
      · intro x y heq
        exact tasteGateAdmissionToEventFlow_injective heq
      · rfl

end BEDC.Derived.TasteGateAdmissionUp
