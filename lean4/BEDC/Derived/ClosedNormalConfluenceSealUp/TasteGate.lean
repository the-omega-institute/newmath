import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedNormalConfluenceSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedNormalConfluenceSealUp : Type where
  | mk :
      (source normal routeLeft routeRight join transport continuation provenance localName :
        BHist) →
      ClosedNormalConfluenceSealUp
  deriving DecidableEq

def closedNormalConfluenceSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedNormalConfluenceSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedNormalConfluenceSealEncodeBHist h

def closedNormalConfluenceSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedNormalConfluenceSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedNormalConfluenceSealDecodeBHist tail)

private theorem closedNormalConfluenceSeal_decode_encode_bhist :
    ∀ h : BHist,
      closedNormalConfluenceSealDecodeBHist
        (closedNormalConfluenceSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def closedNormalConfluenceSealToEventFlow :
    ClosedNormalConfluenceSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedNormalConfluenceSealUp.mk source normal routeLeft routeRight join transport
      continuation provenance localName =>
      [[BMark.b0],
        closedNormalConfluenceSealEncodeBHist source,
        [BMark.b1, BMark.b0],
        closedNormalConfluenceSealEncodeBHist normal,
        [BMark.b1, BMark.b1, BMark.b0],
        closedNormalConfluenceSealEncodeBHist routeLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConfluenceSealEncodeBHist routeRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConfluenceSealEncodeBHist join,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConfluenceSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        closedNormalConfluenceSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        closedNormalConfluenceSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        closedNormalConfluenceSealEncodeBHist localName]

def closedNormalConfluenceSealFromEventFlow :
    EventFlow → Option ClosedNormalConfluenceSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | normal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | routeLeft :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routeRight :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | join :: rest9 =>
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
                                                              | provenance ::
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
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (ClosedNormalConfluenceSealUp.mk
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    source)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    normal)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    routeLeft)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    routeRight)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    join)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    transport)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    continuation)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    provenance)
                                                                                  (closedNormalConfluenceSealDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ =>
                                                                              none

private theorem closedNormalConfluenceSeal_round_trip :
    ∀ x : ClosedNormalConfluenceSealUp,
      closedNormalConfluenceSealFromEventFlow
        (closedNormalConfluenceSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source normal routeLeft routeRight join transport continuation provenance localName =>
      change
        some
          (ClosedNormalConfluenceSealUp.mk
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist source))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist normal))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist routeLeft))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist routeRight))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist join))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist transport))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist continuation))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist provenance))
            (closedNormalConfluenceSealDecodeBHist
              (closedNormalConfluenceSealEncodeBHist localName))) =
          some
            (ClosedNormalConfluenceSealUp.mk source normal routeLeft routeRight join transport
              continuation provenance localName)
      rw [closedNormalConfluenceSeal_decode_encode_bhist source,
        closedNormalConfluenceSeal_decode_encode_bhist normal,
        closedNormalConfluenceSeal_decode_encode_bhist routeLeft,
        closedNormalConfluenceSeal_decode_encode_bhist routeRight,
        closedNormalConfluenceSeal_decode_encode_bhist join,
        closedNormalConfluenceSeal_decode_encode_bhist transport,
        closedNormalConfluenceSeal_decode_encode_bhist continuation,
        closedNormalConfluenceSeal_decode_encode_bhist provenance,
        closedNormalConfluenceSeal_decode_encode_bhist localName]

private theorem closedNormalConfluenceSealToEventFlow_injective
    {x y : ClosedNormalConfluenceSealUp} :
    closedNormalConfluenceSealToEventFlow x =
      closedNormalConfluenceSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedNormalConfluenceSealFromEventFlow
          (closedNormalConfluenceSealToEventFlow x) =
        closedNormalConfluenceSealFromEventFlow
          (closedNormalConfluenceSealToEventFlow y) :=
    congrArg closedNormalConfluenceSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedNormalConfluenceSeal_round_trip x).symm
      (Eq.trans hread (closedNormalConfluenceSeal_round_trip y)))

instance closedNormalConfluenceSealBHistCarrier :
    BHistCarrier ClosedNormalConfluenceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedNormalConfluenceSealToEventFlow
  fromEventFlow := closedNormalConfluenceSealFromEventFlow

instance closedNormalConfluenceSealChapterTasteGate :
    ChapterTasteGate ClosedNormalConfluenceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedNormalConfluenceSealFromEventFlow
        (closedNormalConfluenceSealToEventFlow x) = some x
    exact closedNormalConfluenceSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedNormalConfluenceSealToEventFlow_injective heq)

instance closedNormalConfluenceSealFieldFaithful :
    FieldFaithful ClosedNormalConfluenceSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields
    | ClosedNormalConfluenceSealUp.mk source normal routeLeft routeRight join transport
        continuation provenance localName =>
        [source, normal, routeLeft, routeRight, join, transport, continuation, provenance,
          localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk source normal routeLeft routeRight join transport continuation provenance localName =>
        cases y with
        | mk source' normal' routeLeft' routeRight' join' transport' continuation'
            provenance' localName' =>
            injection hfields with hSource hTail0
            injection hTail0 with hNormal hTail1
            injection hTail1 with hRouteLeft hTail2
            injection hTail2 with hRouteRight hTail3
            injection hTail3 with hJoin hTail4
            injection hTail4 with hTransport hTail5
            injection hTail5 with hContinuation hTail6
            injection hTail6 with hProvenance hTail7
            injection hTail7 with hLocalName _hNil
            cases hSource
            cases hNormal
            cases hRouteLeft
            cases hRouteRight
            cases hJoin
            cases hTransport
            cases hContinuation
            cases hProvenance
            cases hLocalName
            rfl

theorem ClosedNormalConfluenceSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedNormalConfluenceSealDecodeBHist
        (closedNormalConfluenceSealEncodeBHist h) = h) ∧
      (∀ x : ClosedNormalConfluenceSealUp,
        closedNormalConfluenceSealFromEventFlow
          (closedNormalConfluenceSealToEventFlow x) = some x) ∧
        (∀ x y : ClosedNormalConfluenceSealUp,
          closedNormalConfluenceSealToEventFlow x =
            closedNormalConfluenceSealToEventFlow y → x = y) ∧
          closedNormalConfluenceSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact closedNormalConfluenceSeal_decode_encode_bhist
  · constructor
    · exact closedNormalConfluenceSeal_round_trip
    · constructor
      · intro x y heq
        exact closedNormalConfluenceSealToEventFlow_injective heq
      · rfl

end BEDC.Derived.ClosedNormalConfluenceSealUp
