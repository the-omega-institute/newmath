import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModelTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModelTraceUp : Type where
  | mk
      (inferenceState outputTrace corpusSupply auditRefusal largeModelInscription
        observerInterface readback transport route provenance name : BHist) :
      ModelTraceUp
  deriving DecidableEq

def modelTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modelTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modelTraceEncodeBHist h

def modelTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modelTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modelTraceDecodeBHist tail)

private theorem modelTraceDecode_encode_bhist :
    ∀ h : BHist, modelTraceDecodeBHist (modelTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem modelTrace_mk_congr
    {inferenceState inferenceState' outputTrace outputTrace' corpusSupply corpusSupply'
      auditRefusal auditRefusal' largeModelInscription largeModelInscription'
      observerInterface observerInterface' readback readback' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hInferenceState : inferenceState' = inferenceState)
    (hOutputTrace : outputTrace' = outputTrace)
    (hCorpusSupply : corpusSupply' = corpusSupply)
    (hAuditRefusal : auditRefusal' = auditRefusal)
    (hLargeModelInscription : largeModelInscription' = largeModelInscription)
    (hObserverInterface : observerInterface' = observerInterface)
    (hReadback : readback' = readback)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ModelTraceUp.mk inferenceState' outputTrace' corpusSupply' auditRefusal'
        largeModelInscription' observerInterface' readback' transport' route' provenance'
        name' =
      ModelTraceUp.mk inferenceState outputTrace corpusSupply auditRefusal
        largeModelInscription observerInterface readback transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hInferenceState
  cases hOutputTrace
  cases hCorpusSupply
  cases hAuditRefusal
  cases hLargeModelInscription
  cases hObserverInterface
  cases hReadback
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def modelTraceToEventFlow : ModelTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModelTraceUp.mk inferenceState outputTrace corpusSupply auditRefusal largeModelInscription
      observerInterface readback transport route provenance name =>
      [[BMark.b0],
        modelTraceEncodeBHist inferenceState,
        [BMark.b1, BMark.b0],
        modelTraceEncodeBHist outputTrace,
        [BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist corpusSupply,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist auditRefusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist largeModelInscription,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist observerInterface,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modelTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        modelTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modelTraceEncodeBHist name]

private def modelTraceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => modelTraceEventAtDefault index rest

def modelTraceFromEventFlow (ef : EventFlow) : Option ModelTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ModelTraceUp.mk
      (modelTraceDecodeBHist (modelTraceEventAtDefault 1 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 3 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 5 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 7 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 9 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 11 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 13 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 15 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 17 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 19 ef))
      (modelTraceDecodeBHist (modelTraceEventAtDefault 21 ef)))

private theorem modelTrace_round_trip :
    ∀ x : ModelTraceUp, modelTraceFromEventFlow (modelTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inferenceState outputTrace corpusSupply auditRefusal largeModelInscription
      observerInterface readback transport route provenance name =>
      change
        some
          (ModelTraceUp.mk
            (modelTraceDecodeBHist (modelTraceEncodeBHist inferenceState))
            (modelTraceDecodeBHist (modelTraceEncodeBHist outputTrace))
            (modelTraceDecodeBHist (modelTraceEncodeBHist corpusSupply))
            (modelTraceDecodeBHist (modelTraceEncodeBHist auditRefusal))
            (modelTraceDecodeBHist (modelTraceEncodeBHist largeModelInscription))
            (modelTraceDecodeBHist (modelTraceEncodeBHist observerInterface))
            (modelTraceDecodeBHist (modelTraceEncodeBHist readback))
            (modelTraceDecodeBHist (modelTraceEncodeBHist transport))
            (modelTraceDecodeBHist (modelTraceEncodeBHist route))
            (modelTraceDecodeBHist (modelTraceEncodeBHist provenance))
            (modelTraceDecodeBHist (modelTraceEncodeBHist name))) =
          some
            (ModelTraceUp.mk inferenceState outputTrace corpusSupply auditRefusal
              largeModelInscription observerInterface readback transport route provenance name)
      exact
        congrArg some
          (modelTrace_mk_congr
            (modelTraceDecode_encode_bhist inferenceState)
            (modelTraceDecode_encode_bhist outputTrace)
            (modelTraceDecode_encode_bhist corpusSupply)
            (modelTraceDecode_encode_bhist auditRefusal)
            (modelTraceDecode_encode_bhist largeModelInscription)
            (modelTraceDecode_encode_bhist observerInterface)
            (modelTraceDecode_encode_bhist readback)
            (modelTraceDecode_encode_bhist transport)
            (modelTraceDecode_encode_bhist route)
            (modelTraceDecode_encode_bhist provenance)
            (modelTraceDecode_encode_bhist name))

private theorem modelTraceToEventFlow_injective {x y : ModelTraceUp} :
    modelTraceToEventFlow x = modelTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modelTraceFromEventFlow (modelTraceToEventFlow x) =
        modelTraceFromEventFlow (modelTraceToEventFlow y) :=
    congrArg modelTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (modelTrace_round_trip x).symm (Eq.trans hread (modelTrace_round_trip y)))

instance modelTraceBHistCarrier : BHistCarrier ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modelTraceToEventFlow
  fromEventFlow := modelTraceFromEventFlow

instance modelTraceChapterTasteGate : ChapterTasteGate ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change modelTraceFromEventFlow (modelTraceToEventFlow x) = some x
    exact modelTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (modelTraceToEventFlow_injective heq)

instance modelTraceFieldFaithful : FieldFaithful ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ModelTraceUp.mk inferenceState outputTrace corpusSupply auditRefusal
        largeModelInscription observerInterface readback transport route provenance name =>
        [inferenceState, outputTrace, corpusSupply, auditRefusal, largeModelInscription,
          observerInterface, readback, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk inferenceState₁ outputTrace₁ corpusSupply₁ auditRefusal₁ largeModelInscription₁
        observerInterface₁ readback₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk inferenceState₂ outputTrace₂ corpusSupply₂ auditRefusal₂ largeModelInscription₂
            observerInterface₂ readback₂ transport₂ route₂ provenance₂ name₂ =>
            injection h with hInferenceState hRest₁
            injection hRest₁ with hOutputTrace hRest₂
            injection hRest₂ with hCorpusSupply hRest₃
            injection hRest₃ with hAuditRefusal hRest₄
            injection hRest₄ with hLargeModelInscription hRest₅
            injection hRest₅ with hObserverInterface hRest₆
            injection hRest₆ with hReadback hRest₇
            injection hRest₇ with hTransport hRest₈
            injection hRest₈ with hRoute hRest₉
            injection hRest₉ with hProvenance hRest₁₀
            injection hRest₁₀ with hName _
            cases hInferenceState
            cases hOutputTrace
            cases hCorpusSupply
            cases hAuditRefusal
            cases hLargeModelInscription
            cases hObserverInterface
            cases hReadback
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

instance modelTraceNontrivial : Nontrivial ModelTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModelTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ModelTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ModelTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modelTraceChapterTasteGate

theorem ModelTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, modelTraceDecodeBHist (modelTraceEncodeBHist h) = h) ∧
      (∀ x : ModelTraceUp, modelTraceFromEventFlow (modelTraceToEventFlow x) = some x) ∧
        (∀ x y : ModelTraceUp, modelTraceToEventFlow x = modelTraceToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful ModelTraceUp) ∧ Nonempty (Nontrivial ModelTraceUp) ∧
            modelTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact modelTraceDecode_encode_bhist
  · constructor
    · exact modelTrace_round_trip
    · constructor
      · intro x y heq
        exact modelTraceToEventFlow_injective heq
      · constructor
        · exact ⟨modelTraceFieldFaithful⟩
        · constructor
          · exact ⟨modelTraceNontrivial⟩
          · rfl

end BEDC.Derived.ModelTraceUp
