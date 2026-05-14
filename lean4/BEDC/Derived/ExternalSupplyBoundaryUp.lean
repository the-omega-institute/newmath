import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplyBoundaryUp : Type where
  | mk :
      (boundaryName requestedSupply nonInternalization acceptedForm gapLedger gateQuestion
        transport continuation provenance localName : BHist) →
      ExternalSupplyBoundaryUp
  deriving DecidableEq

def externalSupplyBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplyBoundaryEncodeBHist h

def externalSupplyBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplyBoundaryDecodeBHist tail)

private theorem externalSupplyBoundaryDecode_encode_bhist :
    ∀ h : BHist,
      externalSupplyBoundaryDecodeBHist (externalSupplyBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem externalSupplyBoundary_mk_congr
    {boundaryName boundaryName' requestedSupply requestedSupply'
      nonInternalization nonInternalization' acceptedForm acceptedForm'
      gapLedger gapLedger' gateQuestion gateQuestion' transport transport'
      continuation continuation' provenance provenance' localName localName' : BHist}
    (hBoundaryName : boundaryName' = boundaryName)
    (hRequestedSupply : requestedSupply' = requestedSupply)
    (hNonInternalization : nonInternalization' = nonInternalization)
    (hAcceptedForm : acceptedForm' = acceptedForm)
    (hGapLedger : gapLedger' = gapLedger)
    (hGateQuestion : gateQuestion' = gateQuestion)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    ExternalSupplyBoundaryUp.mk boundaryName' requestedSupply' nonInternalization'
        acceptedForm' gapLedger' gateQuestion' transport' continuation' provenance'
        localName' =
      ExternalSupplyBoundaryUp.mk boundaryName requestedSupply nonInternalization
        acceptedForm gapLedger gateQuestion transport continuation provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBoundaryName
  cases hRequestedSupply
  cases hNonInternalization
  cases hAcceptedForm
  cases hGapLedger
  cases hGateQuestion
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalName
  rfl

def externalSupplyBoundaryToEventFlow : ExternalSupplyBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplyBoundaryUp.mk boundaryName requestedSupply nonInternalization acceptedForm
      gapLedger gateQuestion transport continuation provenance localName =>
      [[BMark.b0],
        externalSupplyBoundaryEncodeBHist boundaryName,
        [BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist requestedSupply,
        [BMark.b1, BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist nonInternalization,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist acceptedForm,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist gapLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist gateQuestion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        externalSupplyBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        externalSupplyBoundaryEncodeBHist localName]

def externalSupplyBoundaryFromEventFlow : EventFlow → Option ExternalSupplyBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | boundaryName :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | requestedSupply :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | nonInternalization :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | acceptedForm :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gapLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | gateQuestion :: rest11 =>
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
                                                              | continuation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (ExternalSupplyBoundaryUp.mk
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            boundaryName)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            requestedSupply)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            nonInternalization)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            acceptedForm)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            gapLedger)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            gateQuestion)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            transport)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            continuation)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            provenance)
                                                                                          (externalSupplyBoundaryDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ => none

private theorem externalSupplyBoundary_round_trip :
    ∀ x : ExternalSupplyBoundaryUp,
      externalSupplyBoundaryFromEventFlow (externalSupplyBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundaryName requestedSupply nonInternalization acceptedForm gapLedger gateQuestion
      transport continuation provenance localName =>
      change
        some
          (ExternalSupplyBoundaryUp.mk
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist boundaryName))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist requestedSupply))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist nonInternalization))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist acceptedForm))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist gapLedger))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist gateQuestion))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist transport))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist continuation))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist provenance))
            (externalSupplyBoundaryDecodeBHist
              (externalSupplyBoundaryEncodeBHist localName))) =
          some
            (ExternalSupplyBoundaryUp.mk boundaryName requestedSupply nonInternalization
              acceptedForm gapLedger gateQuestion transport continuation provenance localName)
      exact
        congrArg some
          (externalSupplyBoundary_mk_congr
            (externalSupplyBoundaryDecode_encode_bhist boundaryName)
            (externalSupplyBoundaryDecode_encode_bhist requestedSupply)
            (externalSupplyBoundaryDecode_encode_bhist nonInternalization)
            (externalSupplyBoundaryDecode_encode_bhist acceptedForm)
            (externalSupplyBoundaryDecode_encode_bhist gapLedger)
            (externalSupplyBoundaryDecode_encode_bhist gateQuestion)
            (externalSupplyBoundaryDecode_encode_bhist transport)
            (externalSupplyBoundaryDecode_encode_bhist continuation)
            (externalSupplyBoundaryDecode_encode_bhist provenance)
            (externalSupplyBoundaryDecode_encode_bhist localName))

private theorem externalSupplyBoundaryToEventFlow_injective
    {x y : ExternalSupplyBoundaryUp} :
    externalSupplyBoundaryToEventFlow x = externalSupplyBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplyBoundaryFromEventFlow (externalSupplyBoundaryToEventFlow x) =
        externalSupplyBoundaryFromEventFlow (externalSupplyBoundaryToEventFlow y) :=
    congrArg externalSupplyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalSupplyBoundary_round_trip x).symm
      (Eq.trans hread (externalSupplyBoundary_round_trip y)))

instance externalSupplyBoundaryBHistCarrier : BHistCarrier ExternalSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplyBoundaryToEventFlow
  fromEventFlow := externalSupplyBoundaryFromEventFlow

instance externalSupplyBoundaryChapterTasteGate : ChapterTasteGate ExternalSupplyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change externalSupplyBoundaryFromEventFlow (externalSupplyBoundaryToEventFlow x) = some x
    exact externalSupplyBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplyBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ExternalSupplyBoundaryUp :=
  externalSupplyBoundaryChapterTasteGate

theorem ExternalSupplyBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      externalSupplyBoundaryDecodeBHist (externalSupplyBoundaryEncodeBHist h) = h) ∧
      (∀ x : ExternalSupplyBoundaryUp,
        externalSupplyBoundaryFromEventFlow (externalSupplyBoundaryToEventFlow x) = some x) ∧
        (∀ x y : ExternalSupplyBoundaryUp,
          externalSupplyBoundaryToEventFlow x = externalSupplyBoundaryToEventFlow y → x = y) ∧
          externalSupplyBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact externalSupplyBoundaryDecode_encode_bhist
  · constructor
    · exact externalSupplyBoundary_round_trip
    · constructor
      · intro x y heq
        exact externalSupplyBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.ExternalSupplyBoundaryUp
