import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverResponseAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverResponseAuditUp : Type where
  | mk
      (promptTrace observerInterface inscriptionPoint inscriptionEvent prompt response refusal
        transport continuation provenance nameCert : BHist) :
      ObserverResponseAuditUp
  deriving DecidableEq

def observerResponseAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerResponseAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerResponseAuditEncodeBHist h

def observerResponseAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerResponseAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerResponseAuditDecodeBHist tail)

private theorem observerResponseAuditDecodeEncodeBHist :
    ∀ h : BHist,
      observerResponseAuditDecodeBHist (observerResponseAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observerResponseAuditFields :
    ObserverResponseAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverResponseAuditUp.mk promptTrace observerInterface inscriptionPoint
      inscriptionEvent prompt response refusal transport continuation provenance nameCert =>
      [promptTrace, observerInterface, inscriptionPoint, inscriptionEvent, prompt, response,
        refusal, transport, continuation, provenance, nameCert]

def observerResponseAuditToEventFlow :
    ObserverResponseAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverResponseAuditUp.mk promptTrace observerInterface inscriptionPoint
      inscriptionEvent prompt response refusal transport continuation provenance nameCert =>
      [[BMark.b0],
        observerResponseAuditEncodeBHist promptTrace,
        [BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist observerInterface,
        [BMark.b1, BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist inscriptionPoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist inscriptionEvent,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist prompt,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist response,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerResponseAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerResponseAuditEncodeBHist nameCert]

private def observerResponseAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => observerResponseAuditEventAtDefault index rest

def observerResponseAuditFromEventFlow (ef : EventFlow) : Option ObserverResponseAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ObserverResponseAuditUp.mk
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 1 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 3 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 5 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 7 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 9 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 11 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 13 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 15 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 17 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 19 ef))
      (observerResponseAuditDecodeBHist (observerResponseAuditEventAtDefault 21 ef)))

private theorem observerResponseAudit_mk_congr
    {promptTrace promptTrace' observerInterface observerInterface' inscriptionPoint
      inscriptionPoint' inscriptionEvent inscriptionEvent' prompt prompt' response response'
      refusal refusal' transport transport' continuation continuation' provenance provenance'
      nameCert nameCert' : BHist} :
    promptTrace = promptTrace' →
      observerInterface = observerInterface' →
        inscriptionPoint = inscriptionPoint' →
          inscriptionEvent = inscriptionEvent' →
            prompt = prompt' →
              response = response' →
                refusal = refusal' →
                  transport = transport' →
                    continuation = continuation' →
                      provenance = provenance' →
                        nameCert = nameCert' →
                          ObserverResponseAuditUp.mk promptTrace observerInterface
                              inscriptionPoint inscriptionEvent prompt response refusal
                              transport continuation provenance nameCert =
                            ObserverResponseAuditUp.mk promptTrace' observerInterface'
                              inscriptionPoint' inscriptionEvent' prompt' response' refusal'
                              transport' continuation' provenance' nameCert' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hPromptTrace hObserverInterface hInscriptionPoint hInscriptionEvent hPrompt
    hResponse hRefusal hTransport hContinuation hProvenance hNameCert
  cases hPromptTrace
  cases hObserverInterface
  cases hInscriptionPoint
  cases hInscriptionEvent
  cases hPrompt
  cases hResponse
  cases hRefusal
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

private theorem observerResponseAudit_round_trip :
    ∀ x : ObserverResponseAuditUp,
      observerResponseAuditFromEventFlow (observerResponseAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk promptTrace observerInterface inscriptionPoint inscriptionEvent prompt response refusal
      transport continuation provenance nameCert =>
      change
        some
            (ObserverResponseAuditUp.mk
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist promptTrace))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist observerInterface))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist inscriptionPoint))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist inscriptionEvent))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist prompt))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist response))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist refusal))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist transport))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist continuation))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist provenance))
              (observerResponseAuditDecodeBHist
                (observerResponseAuditEncodeBHist nameCert))) =
          some
            (ObserverResponseAuditUp.mk promptTrace observerInterface inscriptionPoint
              inscriptionEvent prompt response refusal transport continuation provenance
              nameCert)
      exact congrArg some
        (observerResponseAudit_mk_congr
          (observerResponseAuditDecodeEncodeBHist promptTrace)
          (observerResponseAuditDecodeEncodeBHist observerInterface)
          (observerResponseAuditDecodeEncodeBHist inscriptionPoint)
          (observerResponseAuditDecodeEncodeBHist inscriptionEvent)
          (observerResponseAuditDecodeEncodeBHist prompt)
          (observerResponseAuditDecodeEncodeBHist response)
          (observerResponseAuditDecodeEncodeBHist refusal)
          (observerResponseAuditDecodeEncodeBHist transport)
          (observerResponseAuditDecodeEncodeBHist continuation)
          (observerResponseAuditDecodeEncodeBHist provenance)
          (observerResponseAuditDecodeEncodeBHist nameCert))

private theorem observerResponseAuditToEventFlow_injective
    {x y : ObserverResponseAuditUp} :
    observerResponseAuditToEventFlow x = observerResponseAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerResponseAuditFromEventFlow (observerResponseAuditToEventFlow x) =
        observerResponseAuditFromEventFlow (observerResponseAuditToEventFlow y) :=
    congrArg observerResponseAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerResponseAudit_round_trip x).symm
      (Eq.trans hread (observerResponseAudit_round_trip y)))

private theorem observerResponseAudit_fields_faithful :
    ∀ x y : ObserverResponseAuditUp,
      observerResponseAuditFields x = observerResponseAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk promptTrace observerInterface inscriptionPoint inscriptionEvent prompt response refusal
      transport continuation provenance nameCert =>
      cases y with
      | mk promptTrace' observerInterface' inscriptionPoint' inscriptionEvent' prompt'
          response' refusal' transport' continuation' provenance' nameCert' =>
          cases hfields
          rfl

theorem ObserverResponseAuditTasteGate_single_carrier_alignment_round_aux :
    ∀ x : ObserverResponseAuditUp,
      observerResponseAuditFromEventFlow (observerResponseAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  exact observerResponseAudit_round_trip

theorem ObserverResponseAuditTasteGate_single_carrier_alignment_injective_aux :
    ∀ x y : ObserverResponseAuditUp,
      observerResponseAuditToEventFlow x = observerResponseAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  exact observerResponseAuditToEventFlow_injective h

theorem ObserverResponseAuditTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : ObserverResponseAuditUp,
      observerResponseAuditFields x = observerResponseAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  exact observerResponseAudit_fields_faithful

instance observerResponseAuditBHistCarrier :
    BHistCarrier ObserverResponseAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerResponseAuditToEventFlow
  fromEventFlow := observerResponseAuditFromEventFlow

instance observerResponseAuditChapterTasteGate :
    ChapterTasteGate ObserverResponseAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observerResponseAuditFromEventFlow (observerResponseAuditToEventFlow x) = some x
    exact observerResponseAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerResponseAuditToEventFlow_injective heq)

instance observerResponseAuditFieldFaithful :
    FieldFaithful ObserverResponseAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observerResponseAuditFields
  field_faithful := observerResponseAudit_fields_faithful

def taste_gate : ChapterTasteGate ObserverResponseAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerResponseAuditChapterTasteGate

theorem ObserverResponseAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, observerResponseAuditDecodeBHist (observerResponseAuditEncodeBHist h) = h) ∧
      (∀ x : ObserverResponseAuditUp,
        observerResponseAuditFromEventFlow (observerResponseAuditToEventFlow x) = some x) ∧
        (∀ x y : ObserverResponseAuditUp,
          observerResponseAuditToEventFlow x = observerResponseAuditToEventFlow y → x = y) ∧
          observerResponseAuditEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observerResponseAuditDecodeEncodeBHist
  · constructor
    · exact observerResponseAudit_round_trip
    · constructor
      · intro x y heq
        exact observerResponseAuditToEventFlow_injective heq
      · rfl

end BEDC.Derived.ObserverResponseAuditUp
