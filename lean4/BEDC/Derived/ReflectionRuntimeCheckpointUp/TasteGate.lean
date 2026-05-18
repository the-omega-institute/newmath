import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReflectionRuntimeCheckpointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReflectionRuntimeCheckpointUp : Type where
  | mk :
      (runtimeInput checkpointState traceEvidence validationBoundary transport routes
        provenance nameCert : BHist) →
      ReflectionRuntimeCheckpointUp

def reflectionRuntimeCheckpointEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reflectionRuntimeCheckpointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reflectionRuntimeCheckpointEncodeBHist h

def reflectionRuntimeCheckpointDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reflectionRuntimeCheckpointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reflectionRuntimeCheckpointDecodeBHist tail)

private theorem reflectionRuntimeCheckpoint_decode_encode_bhist :
    ∀ h : BHist,
      reflectionRuntimeCheckpointDecodeBHist (reflectionRuntimeCheckpointEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def reflectionRuntimeCheckpointToEventFlow : ReflectionRuntimeCheckpointUp → EventFlow
  | ReflectionRuntimeCheckpointUp.mk runtimeInput checkpointState traceEvidence validationBoundary
      transport routes provenance nameCert =>
      [[BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist runtimeInput,
        [BMark.b1, BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist checkpointState,
        [BMark.b1, BMark.b1, BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist traceEvidence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist validationBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        reflectionRuntimeCheckpointEncodeBHist nameCert]

private def reflectionRuntimeCheckpointDecodePacket
    (runtimeInput checkpointState traceEvidence validationBoundary transport routes provenance
      nameCert : RawEvent) : ReflectionRuntimeCheckpointUp :=
  ReflectionRuntimeCheckpointUp.mk
    (reflectionRuntimeCheckpointDecodeBHist runtimeInput)
    (reflectionRuntimeCheckpointDecodeBHist checkpointState)
    (reflectionRuntimeCheckpointDecodeBHist traceEvidence)
    (reflectionRuntimeCheckpointDecodeBHist validationBoundary)
    (reflectionRuntimeCheckpointDecodeBHist transport)
    (reflectionRuntimeCheckpointDecodeBHist routes)
    (reflectionRuntimeCheckpointDecodeBHist provenance)
    (reflectionRuntimeCheckpointDecodeBHist nameCert)

def reflectionRuntimeCheckpointFromEventFlow :
    EventFlow → Option ReflectionRuntimeCheckpointUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | runtimeInput :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | checkpointState :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | traceEvidence :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | validationBoundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | routes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (reflectionRuntimeCheckpointDecodePacket
                                                                          runtimeInput
                                                                          checkpointState
                                                                          traceEvidence
                                                                          validationBoundary
                                                                          transport
                                                                          routes
                                                                          provenance
                                                                          nameCert)
                                                                  | _ :: _ => none

private theorem reflectionRuntimeCheckpointMkCongr
    {runtimeInput runtimeInput' checkpointState checkpointState' traceEvidence traceEvidence'
      validationBoundary validationBoundary' transport transport' routes routes' provenance
      provenance' nameCert nameCert' : BHist}
    (hRuntimeInput : runtimeInput' = runtimeInput)
    (hCheckpointState : checkpointState' = checkpointState)
    (hTraceEvidence : traceEvidence' = traceEvidence)
    (hValidationBoundary : validationBoundary' = validationBoundary)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    ReflectionRuntimeCheckpointUp.mk runtimeInput' checkpointState' traceEvidence'
        validationBoundary' transport' routes' provenance' nameCert' =
      ReflectionRuntimeCheckpointUp.mk runtimeInput checkpointState traceEvidence
        validationBoundary transport routes provenance nameCert := by
  cases hRuntimeInput
  cases hCheckpointState
  cases hTraceEvidence
  cases hValidationBoundary
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

private theorem reflectionRuntimeCheckpoint_round_trip :
    ∀ x : ReflectionRuntimeCheckpointUp,
      reflectionRuntimeCheckpointFromEventFlow
          (reflectionRuntimeCheckpointToEventFlow x) =
        some x := by
  intro x
  cases x with
  | mk runtimeInput checkpointState traceEvidence validationBoundary transport routes
      provenance nameCert =>
      change
        some
          (reflectionRuntimeCheckpointDecodePacket
            (reflectionRuntimeCheckpointEncodeBHist runtimeInput)
            (reflectionRuntimeCheckpointEncodeBHist checkpointState)
            (reflectionRuntimeCheckpointEncodeBHist traceEvidence)
            (reflectionRuntimeCheckpointEncodeBHist validationBoundary)
            (reflectionRuntimeCheckpointEncodeBHist transport)
            (reflectionRuntimeCheckpointEncodeBHist routes)
            (reflectionRuntimeCheckpointEncodeBHist provenance)
            (reflectionRuntimeCheckpointEncodeBHist nameCert)) =
          some
            (ReflectionRuntimeCheckpointUp.mk runtimeInput checkpointState traceEvidence
              validationBoundary transport routes provenance nameCert)
      unfold reflectionRuntimeCheckpointDecodePacket
      exact
        congrArg some
          (reflectionRuntimeCheckpointMkCongr
            (reflectionRuntimeCheckpoint_decode_encode_bhist runtimeInput)
            (reflectionRuntimeCheckpoint_decode_encode_bhist checkpointState)
            (reflectionRuntimeCheckpoint_decode_encode_bhist traceEvidence)
            (reflectionRuntimeCheckpoint_decode_encode_bhist validationBoundary)
            (reflectionRuntimeCheckpoint_decode_encode_bhist transport)
            (reflectionRuntimeCheckpoint_decode_encode_bhist routes)
            (reflectionRuntimeCheckpoint_decode_encode_bhist provenance)
            (reflectionRuntimeCheckpoint_decode_encode_bhist nameCert))

private theorem reflectionRuntimeCheckpointToEventFlow_injective
    {x y : ReflectionRuntimeCheckpointUp} :
    reflectionRuntimeCheckpointToEventFlow x =
      reflectionRuntimeCheckpointToEventFlow y → x = y := by
  intro heq
  have hread :
      reflectionRuntimeCheckpointFromEventFlow (reflectionRuntimeCheckpointToEventFlow x) =
        reflectionRuntimeCheckpointFromEventFlow (reflectionRuntimeCheckpointToEventFlow y) :=
    congrArg reflectionRuntimeCheckpointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reflectionRuntimeCheckpoint_round_trip x).symm
      (Eq.trans hread (reflectionRuntimeCheckpoint_round_trip y)))

private def reflectionRuntimeCheckpointFields :
    ReflectionRuntimeCheckpointUp → List BHist
  | ReflectionRuntimeCheckpointUp.mk runtimeInput checkpointState traceEvidence validationBoundary
      transport routes provenance nameCert =>
      [runtimeInput, checkpointState, traceEvidence, validationBoundary, transport, routes,
        provenance, nameCert]

private theorem reflectionRuntimeCheckpoint_field_faithful :
    ∀ x y : ReflectionRuntimeCheckpointUp,
      reflectionRuntimeCheckpointFields x = reflectionRuntimeCheckpointFields y → x = y := by
  intro x y hfields
  cases x with
  | mk runtimeInput checkpointState traceEvidence validationBoundary transport routes
      provenance nameCert =>
      cases y with
      | mk runtimeInput' checkpointState' traceEvidence' validationBoundary' transport' routes'
          provenance' nameCert' =>
          cases hfields
          rfl

instance reflectionRuntimeCheckpointBHistCarrier :
    BHistCarrier ReflectionRuntimeCheckpointUp where
  toEventFlow := reflectionRuntimeCheckpointToEventFlow
  fromEventFlow := reflectionRuntimeCheckpointFromEventFlow

instance reflectionRuntimeCheckpointChapterTasteGate :
    ChapterTasteGate ReflectionRuntimeCheckpointUp where
  round_trip := by
    intro x
    change
      reflectionRuntimeCheckpointFromEventFlow
        (reflectionRuntimeCheckpointToEventFlow x) = some x
    exact reflectionRuntimeCheckpoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reflectionRuntimeCheckpointToEventFlow_injective heq)

instance reflectionRuntimeCheckpointFieldFaithful :
    FieldFaithful ReflectionRuntimeCheckpointUp where
  fields := reflectionRuntimeCheckpointFields
  field_faithful := reflectionRuntimeCheckpoint_field_faithful

instance reflectionRuntimeCheckpointNontrivial :
    Nontrivial ReflectionRuntimeCheckpointUp where
  witness_pair :=
    ⟨ReflectionRuntimeCheckpointUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ReflectionRuntimeCheckpointUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ReflectionRuntimeCheckpointUp :=
  reflectionRuntimeCheckpointChapterTasteGate

theorem ReflectionRuntimeCheckpointTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ReflectionRuntimeCheckpointUp) ∧
      Nonempty (FieldFaithful ReflectionRuntimeCheckpointUp) ∧
      Nonempty (Nontrivial ReflectionRuntimeCheckpointUp) ∧
        (∀ h : BHist,
          reflectionRuntimeCheckpointDecodeBHist
            (reflectionRuntimeCheckpointEncodeBHist h) = h) ∧
          reflectionRuntimeCheckpointEncodeBHist BHist.Empty = ([] : List BMark) := by
  exact
    ⟨⟨reflectionRuntimeCheckpointChapterTasteGate⟩,
      ⟨reflectionRuntimeCheckpointFieldFaithful⟩,
      ⟨reflectionRuntimeCheckpointNontrivial⟩, reflectionRuntimeCheckpoint_decode_encode_bhist,
      rfl⟩

theorem ReflectionRuntimeCheckpointUp_StdBridge :
    Nonempty (ChapterTasteGate ReflectionRuntimeCheckpointUp) ∧
      (∀ (x : ReflectionRuntimeCheckpointUp) (w : RawEvent) (m : BMark),
        List.Mem w (BHistCarrier.toEventFlow x) → List.Mem m w →
          m = BMark.b0 ∨ m = BMark.b1) ∧
        (∀ x : ReflectionRuntimeCheckpointUp,
          ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow ChapterTasteGate BHistCarrier
  exact
    ⟨⟨reflectionRuntimeCheckpointChapterTasteGate⟩,
      ChapterTasteGate.conservativity,
      ChapterTasteGate.no_hidden_input⟩

end BEDC.Derived.ReflectionRuntimeCheckpointUp
