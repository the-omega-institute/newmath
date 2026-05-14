import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniversalClosedSubstrateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniversalClosedSubstrateUp : Type where
  | mk
      (ruleTable closedObservation encoding simulatorStep trace boundary transport
        continuation provenance nameCert : BHist) :
      UniversalClosedSubstrateUp
  deriving DecidableEq

private def universalClosedSubstrateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: universalClosedSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: universalClosedSubstrateEncodeBHist h

private def universalClosedSubstrateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (universalClosedSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (universalClosedSubstrateDecodeBHist tail)

private theorem universalClosedSubstrate_decode_encode_bhist :
    ∀ h : BHist,
      universalClosedSubstrateDecodeBHist
        (universalClosedSubstrateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def universalClosedSubstrateToEventFlow :
    UniversalClosedSubstrateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniversalClosedSubstrateUp.mk ruleTable closedObservation encoding simulatorStep
      trace boundary transport continuation provenance nameCert =>
      [[BMark.b0],
        universalClosedSubstrateEncodeBHist ruleTable,
        [BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist closedObservation,
        [BMark.b1, BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist encoding,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist simulatorStep,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        universalClosedSubstrateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        universalClosedSubstrateEncodeBHist nameCert]

private def universalClosedSubstrateFromEventFlow :
    EventFlow → Option UniversalClosedSubstrateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | ruleTable :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closedObservation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | encoding :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | simulatorStep :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | trace :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | boundary :: rest11 =>
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
                                                              | continuation ::
                                                                  rest15 =>
                                                                  match rest15
                                                                    with
                                                                  | [] => none
                                                                  | _tag8 ::
                                                                      rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] =>
                                                                          none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] =>
                                                                                  none
                                                                              | nameCert ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      some
                                                                                        (UniversalClosedSubstrateUp.mk
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            ruleTable)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            closedObservation)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            encoding)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            simulatorStep)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            trace)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            boundary)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            transport)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            continuation)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            provenance)
                                                                                          (universalClosedSubstrateDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem universalClosedSubstrate_round_trip :
    ∀ x : UniversalClosedSubstrateUp,
      universalClosedSubstrateFromEventFlow
        (universalClosedSubstrateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ruleTable closedObservation encoding simulatorStep trace boundary transport
      continuation provenance nameCert =>
      change
        some
          (UniversalClosedSubstrateUp.mk
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist ruleTable))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist closedObservation))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist encoding))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist simulatorStep))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist trace))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist boundary))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist transport))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist continuation))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist provenance))
            (universalClosedSubstrateDecodeBHist
              (universalClosedSubstrateEncodeBHist nameCert))) =
          some
            (UniversalClosedSubstrateUp.mk ruleTable closedObservation encoding
              simulatorStep trace boundary transport continuation provenance nameCert)
      rw [universalClosedSubstrate_decode_encode_bhist ruleTable,
        universalClosedSubstrate_decode_encode_bhist closedObservation,
        universalClosedSubstrate_decode_encode_bhist encoding,
        universalClosedSubstrate_decode_encode_bhist simulatorStep,
        universalClosedSubstrate_decode_encode_bhist trace,
        universalClosedSubstrate_decode_encode_bhist boundary,
        universalClosedSubstrate_decode_encode_bhist transport,
        universalClosedSubstrate_decode_encode_bhist continuation,
        universalClosedSubstrate_decode_encode_bhist provenance,
        universalClosedSubstrate_decode_encode_bhist nameCert]

private theorem universalClosedSubstrateToEventFlow_injective
    {x y : UniversalClosedSubstrateUp} :
    universalClosedSubstrateToEventFlow x =
      universalClosedSubstrateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      universalClosedSubstrateFromEventFlow
          (universalClosedSubstrateToEventFlow x) =
        universalClosedSubstrateFromEventFlow
          (universalClosedSubstrateToEventFlow y) :=
    congrArg universalClosedSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (universalClosedSubstrate_round_trip x).symm
      (Eq.trans hread (universalClosedSubstrate_round_trip y)))

private def universalClosedSubstrateFields :
    UniversalClosedSubstrateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniversalClosedSubstrateUp.mk ruleTable closedObservation encoding simulatorStep trace
      boundary transport continuation provenance nameCert =>
      [ruleTable, closedObservation, encoding, simulatorStep, trace, boundary, transport,
        continuation, provenance, nameCert]

private theorem universalClosedSubstrate_field_faithful :
    ∀ x y : UniversalClosedSubstrateUp,
      universalClosedSubstrateFields x = universalClosedSubstrateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk ruleTable closedObservation encoding simulatorStep trace boundary transport
      continuation provenance nameCert =>
      cases y with
      | mk ruleTable' closedObservation' encoding' simulatorStep' trace' boundary'
          transport' continuation' provenance' nameCert' =>
          cases hfields
          rfl

instance universalClosedSubstrateBHistCarrier :
    BHistCarrier UniversalClosedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := universalClosedSubstrateToEventFlow
  fromEventFlow := universalClosedSubstrateFromEventFlow

instance universalClosedSubstrateChapterTasteGate :
    ChapterTasteGate UniversalClosedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      universalClosedSubstrateFromEventFlow
        (universalClosedSubstrateToEventFlow x) = some x
    exact universalClosedSubstrate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (universalClosedSubstrateToEventFlow_injective heq)

instance universalClosedSubstrateFieldFaithful :
    FieldFaithful UniversalClosedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := universalClosedSubstrateFields
  field_faithful := universalClosedSubstrate_field_faithful

instance universalClosedSubstrateNontrivial :
    Nontrivial UniversalClosedSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniversalClosedSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniversalClosedSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniversalClosedSubstrateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  universalClosedSubstrateChapterTasteGate

theorem UniversalClosedSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      universalClosedSubstrateDecodeBHist
        (universalClosedSubstrateEncodeBHist h) = h) ∧
      (∀ x : UniversalClosedSubstrateUp,
        universalClosedSubstrateFromEventFlow
          (universalClosedSubstrateToEventFlow x) = some x) ∧
        (∀ x y : UniversalClosedSubstrateUp,
          universalClosedSubstrateToEventFlow x =
            universalClosedSubstrateToEventFlow y → x = y) ∧
          universalClosedSubstrateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨universalClosedSubstrate_decode_encode_bhist, universalClosedSubstrate_round_trip,
      (fun _ _ heq => universalClosedSubstrateToEventFlow_injective heq), rfl⟩

end BEDC.Derived.UniversalClosedSubstrateUp
