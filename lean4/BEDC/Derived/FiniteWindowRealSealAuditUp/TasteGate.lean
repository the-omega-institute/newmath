import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowRealSealAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowRealSealAuditUp : Type where
  | mk : (window dyadic regseq realSeal refusal transport continuation provenance name : BHist) →
      FiniteWindowRealSealAuditUp
  deriving DecidableEq

def finiteWindowRealSealAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowRealSealAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowRealSealAuditEncodeBHist h

def finiteWindowRealSealAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowRealSealAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowRealSealAuditDecodeBHist tail)

private theorem finiteWindowRealSealAudit_decode_encode_bhist :
    ∀ h : BHist,
      finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteWindowRealSealAuditFields :
    FiniteWindowRealSealAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowRealSealAuditUp.mk window dyadic regseq realSeal refusal transport
      continuation provenance name =>
      [window, dyadic, regseq, realSeal, refusal, transport, continuation, provenance, name]

def finiteWindowRealSealAuditToEventFlow :
    FiniteWindowRealSealAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowRealSealAuditUp.mk window dyadic regseq realSeal refusal transport
      continuation provenance name =>
      [[BMark.b0],
        finiteWindowRealSealAuditEncodeBHist window,
        [BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist regseq,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteWindowRealSealAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteWindowRealSealAuditEncodeBHist name]

def finiteWindowRealSealAuditFromEventFlow :
    EventFlow → Option FiniteWindowRealSealAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | dyadic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regseq :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
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
                                                                                (FiniteWindowRealSealAuditUp.mk
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    window)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    dyadic)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    regseq)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    realSeal)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    refusal)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    transport)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    continuation)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    provenance)
                                                                                  (finiteWindowRealSealAuditDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem finiteWindowRealSealAudit_round_trip_mk_congr
    {window window' dyadic dyadic' regseq regseq' realSeal realSeal' refusal refusal'
      transport transport' continuation continuation' provenance provenance' name name' : BHist} :
    window = window' →
      dyadic = dyadic' →
        regseq = regseq' →
          realSeal = realSeal' →
            refusal = refusal' →
              transport = transport' →
                continuation = continuation' →
                  provenance = provenance' →
                    name = name' →
                      FiniteWindowRealSealAuditUp.mk window dyadic regseq realSeal refusal
                          transport continuation provenance name =
                        FiniteWindowRealSealAuditUp.mk window' dyadic' regseq' realSeal'
                          refusal' transport' continuation' provenance' name' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hWindow hDyadic hRegseq hRealSeal hRefusal hTransport hContinuation hProvenance
    hName
  cases hWindow
  cases hDyadic
  cases hRegseq
  cases hRealSeal
  cases hRefusal
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

theorem finiteWindowRealSealAudit_round_trip :
    ∀ x : FiniteWindowRealSealAuditUp,
      finiteWindowRealSealAuditFromEventFlow
        (finiteWindowRealSealAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window dyadic regseq realSeal refusal transport continuation provenance name =>
      change
        some
          (FiniteWindowRealSealAuditUp.mk
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist window))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist dyadic))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist regseq))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist realSeal))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist refusal))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist transport))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist continuation))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist provenance))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist name))) =
          some
            (FiniteWindowRealSealAuditUp.mk window dyadic regseq realSeal refusal transport
              continuation provenance name)
      have hWindow :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist window) = window :=
        finiteWindowRealSealAudit_decode_encode_bhist window
      have hDyadic :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist dyadic) = dyadic :=
        finiteWindowRealSealAudit_decode_encode_bhist dyadic
      have hRegseq :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist regseq) = regseq :=
        finiteWindowRealSealAudit_decode_encode_bhist regseq
      have hRealSeal :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist realSeal) = realSeal :=
        finiteWindowRealSealAudit_decode_encode_bhist realSeal
      have hRefusal :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist refusal) = refusal :=
        finiteWindowRealSealAudit_decode_encode_bhist refusal
      have hTransport :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist transport) = transport :=
        finiteWindowRealSealAudit_decode_encode_bhist transport
      have hContinuation :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist continuation) = continuation :=
        finiteWindowRealSealAudit_decode_encode_bhist continuation
      have hProvenance :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist provenance) = provenance :=
        finiteWindowRealSealAudit_decode_encode_bhist provenance
      have hName :
          finiteWindowRealSealAuditDecodeBHist
            (finiteWindowRealSealAuditEncodeBHist name) = name :=
        finiteWindowRealSealAudit_decode_encode_bhist name
      exact congrArg some
        (finiteWindowRealSealAudit_round_trip_mk_congr hWindow hDyadic hRegseq hRealSeal
          hRefusal hTransport hContinuation hProvenance hName)

private theorem finiteWindowRealSealAuditToEventFlow_injective
    {x y : FiniteWindowRealSealAuditUp} :
    finiteWindowRealSealAuditToEventFlow x =
      finiteWindowRealSealAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowRealSealAuditFromEventFlow
          (finiteWindowRealSealAuditToEventFlow x) =
        finiteWindowRealSealAuditFromEventFlow
          (finiteWindowRealSealAuditToEventFlow y) :=
    congrArg finiteWindowRealSealAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteWindowRealSealAudit_round_trip x).symm
      (Eq.trans hread (finiteWindowRealSealAudit_round_trip y)))

private theorem finiteWindowRealSealAudit_field_faithful :
    ∀ x y : FiniteWindowRealSealAuditUp,
      finiteWindowRealSealAuditFields x =
        finiteWindowRealSealAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk window dyadic regseq realSeal refusal transport continuation provenance name =>
      cases y with
      | mk window' dyadic' regseq' realSeal' refusal' transport' continuation' provenance'
          name' =>
          cases hfields
          rfl

instance finiteWindowRealSealAuditBHistCarrier :
    BHistCarrier FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowRealSealAuditToEventFlow
  fromEventFlow := finiteWindowRealSealAuditFromEventFlow

instance finiteWindowRealSealAuditChapterTasteGate :
    ChapterTasteGate FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteWindowRealSealAuditFromEventFlow
        (finiteWindowRealSealAuditToEventFlow x) = some x
    exact finiteWindowRealSealAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowRealSealAuditToEventFlow_injective heq)

instance finiteWindowRealSealAuditFieldFaithful :
    FieldFaithful FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowRealSealAuditFields
  field_faithful := finiteWindowRealSealAudit_field_faithful

instance finiteWindowRealSealAuditNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowRealSealAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteWindowRealSealAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteWindowRealSealAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowRealSealAuditChapterTasteGate

end BEDC.Derived.FiniteWindowRealSealAuditUp
