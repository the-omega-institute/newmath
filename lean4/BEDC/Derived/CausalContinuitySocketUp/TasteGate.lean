import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CausalContinuitySocketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CausalContinuitySocketUp : Type where
  | mk :
      (record prediction gate socket transport route provenance name : BHist) →
      CausalContinuitySocketUp
  deriving DecidableEq

def causalContinuitySocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: causalContinuitySocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: causalContinuitySocketEncodeBHist h

def causalContinuitySocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (causalContinuitySocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (causalContinuitySocketDecodeBHist tail)

private theorem causalContinuitySocket_decode_encode_bhist :
    ∀ h : BHist,
      causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def causalContinuitySocketFields : CausalContinuitySocketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CausalContinuitySocketUp.mk record prediction gate socket transport route provenance name =>
      [record, prediction, gate, socket, transport, route, provenance, name]

def causalContinuitySocketToEventFlow : CausalContinuitySocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CausalContinuitySocketUp.mk record prediction gate socket transport route provenance name =>
      [[BMark.b0],
        causalContinuitySocketEncodeBHist record,
        [BMark.b1, BMark.b0],
        causalContinuitySocketEncodeBHist prediction,
        [BMark.b1, BMark.b1, BMark.b0],
        causalContinuitySocketEncodeBHist gate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        causalContinuitySocketEncodeBHist socket,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        causalContinuitySocketEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        causalContinuitySocketEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        causalContinuitySocketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        causalContinuitySocketEncodeBHist name]

def causalContinuitySocketFromEventFlow : EventFlow → Option CausalContinuitySocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | record :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | prediction :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gate :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | socket :: rest7 =>
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
                                              | route :: rest11 =>
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
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (CausalContinuitySocketUp.mk
                                                                          (causalContinuitySocketDecodeBHist
                                                                            record)
                                                                          (causalContinuitySocketDecodeBHist
                                                                            prediction)
                                                                          (causalContinuitySocketDecodeBHist
                                                                            gate)
                                                                          (causalContinuitySocketDecodeBHist
                                                                            socket)
                                                                          (causalContinuitySocketDecodeBHist
                                                                            transport)
                                                                          (causalContinuitySocketDecodeBHist
                                                                            route)
                                                                          (causalContinuitySocketDecodeBHist
                                                                            provenance)
                                                                          (causalContinuitySocketDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem causalContinuitySocket_round_trip :
    ∀ x : CausalContinuitySocketUp,
      causalContinuitySocketFromEventFlow (causalContinuitySocketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk record prediction gate socket transport route provenance name =>
      change
        some
          (CausalContinuitySocketUp.mk
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist record))
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist prediction))
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist gate))
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist socket))
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist transport))
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist route))
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist provenance))
            (causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist name))) =
          some
            (CausalContinuitySocketUp.mk record prediction gate socket transport route provenance
              name)
      rw [causalContinuitySocket_decode_encode_bhist record,
        causalContinuitySocket_decode_encode_bhist prediction,
        causalContinuitySocket_decode_encode_bhist gate,
        causalContinuitySocket_decode_encode_bhist socket,
        causalContinuitySocket_decode_encode_bhist transport,
        causalContinuitySocket_decode_encode_bhist route,
        causalContinuitySocket_decode_encode_bhist provenance,
        causalContinuitySocket_decode_encode_bhist name]

private theorem causalContinuitySocketToEventFlow_injective {x y : CausalContinuitySocketUp} :
    causalContinuitySocketToEventFlow x = causalContinuitySocketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      causalContinuitySocketFromEventFlow (causalContinuitySocketToEventFlow x) =
        causalContinuitySocketFromEventFlow (causalContinuitySocketToEventFlow y) :=
    congrArg causalContinuitySocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (causalContinuitySocket_round_trip x).symm
      (Eq.trans hread (causalContinuitySocket_round_trip y)))

private theorem CausalContinuitySocketTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CausalContinuitySocketUp,
      causalContinuitySocketFields x = causalContinuitySocketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk record prediction gate socket transport route provenance name =>
      cases y with
      | mk record' prediction' gate' socket' transport' route' provenance' name' =>
          cases hfields
          rfl

instance causalContinuitySocketBHistCarrier : BHistCarrier CausalContinuitySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := causalContinuitySocketToEventFlow
  fromEventFlow := causalContinuitySocketFromEventFlow

instance causalContinuitySocketChapterTasteGate :
    ChapterTasteGate CausalContinuitySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change causalContinuitySocketFromEventFlow (causalContinuitySocketToEventFlow x) = some x
    exact causalContinuitySocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (causalContinuitySocketToEventFlow_injective heq)

instance causalContinuitySocketFieldFaithful : FieldFaithful CausalContinuitySocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := causalContinuitySocketFields
  field_faithful := CausalContinuitySocketTasteGate_single_carrier_alignment_field_faithful

theorem CausalContinuitySocketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      causalContinuitySocketDecodeBHist (causalContinuitySocketEncodeBHist h) = h) ∧
      (∀ x : CausalContinuitySocketUp,
        causalContinuitySocketFromEventFlow (causalContinuitySocketToEventFlow x) = some x) ∧
        (∀ x y : CausalContinuitySocketUp,
          causalContinuitySocketToEventFlow x = causalContinuitySocketToEventFlow y → x = y) ∧
          causalContinuitySocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact causalContinuitySocket_decode_encode_bhist
  · constructor
    · exact causalContinuitySocket_round_trip
    · constructor
      · intro x y heq
        exact causalContinuitySocketToEventFlow_injective heq
      · rfl

end BEDC.Derived.CausalContinuitySocketUp
