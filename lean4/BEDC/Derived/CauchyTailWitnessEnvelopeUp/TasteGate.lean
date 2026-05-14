import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailWitnessEnvelopeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailWitnessEnvelopeUp : Type where
  | mk
      (selectedWindow finiteWindowEnvelope tailComparison tailAgreementSeal realReadback
        transport continuation provenance nameCert : BHist) :
      CauchyTailWitnessEnvelopeUp
  deriving DecidableEq

def cauchyTailWitnessEnvelopeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailWitnessEnvelopeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailWitnessEnvelopeEncodeBHist h

def cauchyTailWitnessEnvelopeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailWitnessEnvelopeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailWitnessEnvelopeDecodeBHist tail)

private theorem cauchyTailWitnessEnvelope_decode_encode_bhist :
    ∀ h : BHist,
      cauchyTailWitnessEnvelopeDecodeBHist
          (cauchyTailWitnessEnvelopeEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyTailWitnessEnvelope_mk_congr
    {selectedWindow selectedWindow' finiteWindowEnvelope finiteWindowEnvelope'
      tailComparison tailComparison' tailAgreementSeal tailAgreementSeal'
      realReadback realReadback' transport transport' continuation continuation'
      provenance provenance' nameCert nameCert' : BHist} :
    selectedWindow = selectedWindow' →
      finiteWindowEnvelope = finiteWindowEnvelope' →
        tailComparison = tailComparison' →
          tailAgreementSeal = tailAgreementSeal' →
            realReadback = realReadback' →
              transport = transport' →
                continuation = continuation' →
                  provenance = provenance' →
                    nameCert = nameCert' →
                      CauchyTailWitnessEnvelopeUp.mk selectedWindow finiteWindowEnvelope
                          tailComparison tailAgreementSeal realReadback transport
                          continuation provenance nameCert =
                        CauchyTailWitnessEnvelopeUp.mk selectedWindow'
                          finiteWindowEnvelope' tailComparison' tailAgreementSeal'
                          realReadback' transport' continuation' provenance' nameCert' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hSelected hEnvelope hComparison hSeal hReadback hTransport hContinuation
    hProvenance hNameCert
  cases hSelected
  cases hEnvelope
  cases hComparison
  cases hSeal
  cases hReadback
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

def cauchyTailWitnessEnvelopeToEventFlow :
    CauchyTailWitnessEnvelopeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailWitnessEnvelopeUp.mk selectedWindow finiteWindowEnvelope tailComparison
      tailAgreementSeal realReadback transport continuation provenance nameCert =>
      [[BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist selectedWindow,
        [BMark.b1, BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist finiteWindowEnvelope,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist tailComparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist tailAgreementSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist realReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyTailWitnessEnvelopeEncodeBHist nameCert]

def cauchyTailWitnessEnvelopeFromEventFlow :
    EventFlow → Option CauchyTailWitnessEnvelopeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | selectedWindow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | finiteWindowEnvelope :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | tailComparison :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tailAgreementSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realReadback :: rest9 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (CauchyTailWitnessEnvelopeUp.mk
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist selectedWindow)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist finiteWindowEnvelope)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist tailComparison)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist tailAgreementSeal)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist realReadback)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist transport)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist continuation)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist provenance)
                                                                                  (cauchyTailWitnessEnvelopeDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem cauchyTailWitnessEnvelope_round_trip :
    ∀ x : CauchyTailWitnessEnvelopeUp,
      cauchyTailWitnessEnvelopeFromEventFlow
          (cauchyTailWitnessEnvelopeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk selectedWindow finiteWindowEnvelope tailComparison tailAgreementSeal realReadback
      transport continuation provenance nameCert =>
      change
        some
            (CauchyTailWitnessEnvelopeUp.mk
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist selectedWindow))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist finiteWindowEnvelope))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist tailComparison))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist tailAgreementSeal))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist realReadback))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist transport))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist continuation))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist provenance))
              (cauchyTailWitnessEnvelopeDecodeBHist
                (cauchyTailWitnessEnvelopeEncodeBHist nameCert))) =
          some
            (CauchyTailWitnessEnvelopeUp.mk selectedWindow finiteWindowEnvelope
              tailComparison tailAgreementSeal realReadback transport continuation provenance
              nameCert)
      exact congrArg some
        (cauchyTailWitnessEnvelope_mk_congr
          (cauchyTailWitnessEnvelope_decode_encode_bhist selectedWindow)
          (cauchyTailWitnessEnvelope_decode_encode_bhist finiteWindowEnvelope)
          (cauchyTailWitnessEnvelope_decode_encode_bhist tailComparison)
          (cauchyTailWitnessEnvelope_decode_encode_bhist tailAgreementSeal)
          (cauchyTailWitnessEnvelope_decode_encode_bhist realReadback)
          (cauchyTailWitnessEnvelope_decode_encode_bhist transport)
          (cauchyTailWitnessEnvelope_decode_encode_bhist continuation)
          (cauchyTailWitnessEnvelope_decode_encode_bhist provenance)
          (cauchyTailWitnessEnvelope_decode_encode_bhist nameCert))

private theorem cauchyTailWitnessEnvelopeToEventFlow_injective
    {x y : CauchyTailWitnessEnvelopeUp} :
    cauchyTailWitnessEnvelopeToEventFlow x =
      cauchyTailWitnessEnvelopeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailWitnessEnvelopeFromEventFlow
          (cauchyTailWitnessEnvelopeToEventFlow x) =
        cauchyTailWitnessEnvelopeFromEventFlow
          (cauchyTailWitnessEnvelopeToEventFlow y) :=
    congrArg cauchyTailWitnessEnvelopeFromEventFlow heq
  have someSame :
      some x = some y :=
    Eq.trans (cauchyTailWitnessEnvelope_round_trip x).symm
      (Eq.trans hread (cauchyTailWitnessEnvelope_round_trip y))
  cases someSame
  rfl

instance cauchyTailWitnessEnvelopeBHistCarrier :
    BHistCarrier CauchyTailWitnessEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailWitnessEnvelopeToEventFlow
  fromEventFlow := cauchyTailWitnessEnvelopeFromEventFlow

instance cauchyTailWitnessEnvelopeChapterTasteGate :
    ChapterTasteGate CauchyTailWitnessEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyTailWitnessEnvelopeFromEventFlow
          (cauchyTailWitnessEnvelopeToEventFlow x) =
        some x
    exact cauchyTailWitnessEnvelope_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailWitnessEnvelopeToEventFlow_injective heq)

instance cauchyTailWitnessEnvelopeFieldFaithful :
    FieldFaithful CauchyTailWitnessEnvelopeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CauchyTailWitnessEnvelopeUp.mk selectedWindow finiteWindowEnvelope tailComparison
        tailAgreementSeal realReadback transport continuation provenance nameCert =>
        [selectedWindow, finiteWindowEnvelope, tailComparison, tailAgreementSeal,
          realReadback, transport, continuation, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk selectedWindow finiteWindowEnvelope tailComparison tailAgreementSeal realReadback
        transport continuation provenance nameCert =>
        cases y with
        | mk selectedWindow' finiteWindowEnvelope' tailComparison' tailAgreementSeal'
            realReadback' transport' continuation' provenance' nameCert' =>
            cases hfields
            rfl

def taste_gate : ChapterTasteGate CauchyTailWitnessEnvelopeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailWitnessEnvelopeChapterTasteGate

theorem CauchyTailWitnessEnvelopeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyTailWitnessEnvelopeDecodeBHist
        (cauchyTailWitnessEnvelopeEncodeBHist h) = h) ∧
      (∀ x : CauchyTailWitnessEnvelopeUp,
        cauchyTailWitnessEnvelopeFromEventFlow
          (cauchyTailWitnessEnvelopeToEventFlow x) = some x) ∧
        (∀ x y : CauchyTailWitnessEnvelopeUp,
          cauchyTailWitnessEnvelopeToEventFlow x =
            cauchyTailWitnessEnvelopeToEventFlow y →
            x = y) ∧
          cauchyTailWitnessEnvelopeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyTailWitnessEnvelope_decode_encode_bhist,
      cauchyTailWitnessEnvelope_round_trip,
      (fun _x _y sameFlow => cauchyTailWitnessEnvelopeToEventFlow_injective sameFlow),
      rfl⟩

end BEDC.Derived.CauchyTailWitnessEnvelopeUp
