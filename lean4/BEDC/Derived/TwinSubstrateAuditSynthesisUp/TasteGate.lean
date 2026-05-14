import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TwinSubstrateAuditSynthesisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TwinSubstrateAuditSynthesisUp : Type where
  | mk : (metacic ground frontier transport route provenance name : BHist) →
      TwinSubstrateAuditSynthesisUp
  deriving DecidableEq

def twinSubstrateAuditSynthesisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: twinSubstrateAuditSynthesisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: twinSubstrateAuditSynthesisEncodeBHist h

def twinSubstrateAuditSynthesisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (twinSubstrateAuditSynthesisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (twinSubstrateAuditSynthesisDecodeBHist tail)

private theorem twinSubstrateAuditSynthesisDecode_encode_bhist :
    ∀ h : BHist,
      twinSubstrateAuditSynthesisDecodeBHist
          (twinSubstrateAuditSynthesisEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem twinSubstrateAuditSynthesis_mk_congr
    {metacic metacic' ground ground' frontier frontier' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hMetaCIC : metacic' = metacic)
    (hGround : ground' = ground)
    (hFrontier : frontier' = frontier)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    TwinSubstrateAuditSynthesisUp.mk metacic' ground' frontier' transport' route'
        provenance' name' =
      TwinSubstrateAuditSynthesisUp.mk metacic ground frontier transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMetaCIC
  cases hGround
  cases hFrontier
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def twinSubstrateAuditSynthesisToEventFlow : TwinSubstrateAuditSynthesisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TwinSubstrateAuditSynthesisUp.mk metacic ground frontier transport route provenance name =>
      [[BMark.b0],
        twinSubstrateAuditSynthesisEncodeBHist metacic,
        [BMark.b1, BMark.b0],
        twinSubstrateAuditSynthesisEncodeBHist ground,
        [BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditSynthesisEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditSynthesisEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditSynthesisEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditSynthesisEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        twinSubstrateAuditSynthesisEncodeBHist name]

def twinSubstrateAuditSynthesisFromEventFlow :
    EventFlow → Option TwinSubstrateAuditSynthesisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | metacic :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | ground :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | frontier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | route :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | name :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (TwinSubstrateAuditSynthesisUp.mk
                                                                  (twinSubstrateAuditSynthesisDecodeBHist
                                                                    metacic)
                                                                  (twinSubstrateAuditSynthesisDecodeBHist
                                                                    ground)
                                                                  (twinSubstrateAuditSynthesisDecodeBHist
                                                                    frontier)
                                                                  (twinSubstrateAuditSynthesisDecodeBHist
                                                                    transport)
                                                                  (twinSubstrateAuditSynthesisDecodeBHist
                                                                    route)
                                                                  (twinSubstrateAuditSynthesisDecodeBHist
                                                                    provenance)
                                                                  (twinSubstrateAuditSynthesisDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem twinSubstrateAuditSynthesis_round_trip :
    ∀ x : TwinSubstrateAuditSynthesisUp,
      twinSubstrateAuditSynthesisFromEventFlow
          (twinSubstrateAuditSynthesisToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metacic ground frontier transport route provenance name =>
      change
        some
          (TwinSubstrateAuditSynthesisUp.mk
            (twinSubstrateAuditSynthesisDecodeBHist
              (twinSubstrateAuditSynthesisEncodeBHist metacic))
            (twinSubstrateAuditSynthesisDecodeBHist
              (twinSubstrateAuditSynthesisEncodeBHist ground))
            (twinSubstrateAuditSynthesisDecodeBHist
              (twinSubstrateAuditSynthesisEncodeBHist frontier))
            (twinSubstrateAuditSynthesisDecodeBHist
              (twinSubstrateAuditSynthesisEncodeBHist transport))
            (twinSubstrateAuditSynthesisDecodeBHist
              (twinSubstrateAuditSynthesisEncodeBHist route))
            (twinSubstrateAuditSynthesisDecodeBHist
              (twinSubstrateAuditSynthesisEncodeBHist provenance))
            (twinSubstrateAuditSynthesisDecodeBHist
              (twinSubstrateAuditSynthesisEncodeBHist name))) =
          some
            (TwinSubstrateAuditSynthesisUp.mk metacic ground frontier transport route provenance
              name)
      exact
        congrArg some
          (twinSubstrateAuditSynthesis_mk_congr
            (twinSubstrateAuditSynthesisDecode_encode_bhist metacic)
            (twinSubstrateAuditSynthesisDecode_encode_bhist ground)
            (twinSubstrateAuditSynthesisDecode_encode_bhist frontier)
            (twinSubstrateAuditSynthesisDecode_encode_bhist transport)
            (twinSubstrateAuditSynthesisDecode_encode_bhist route)
            (twinSubstrateAuditSynthesisDecode_encode_bhist provenance)
            (twinSubstrateAuditSynthesisDecode_encode_bhist name))

private theorem twinSubstrateAuditSynthesisToEventFlow_injective
    {x y : TwinSubstrateAuditSynthesisUp} :
    twinSubstrateAuditSynthesisToEventFlow x =
      twinSubstrateAuditSynthesisToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      twinSubstrateAuditSynthesisFromEventFlow (twinSubstrateAuditSynthesisToEventFlow x) =
        twinSubstrateAuditSynthesisFromEventFlow (twinSubstrateAuditSynthesisToEventFlow y) :=
    congrArg twinSubstrateAuditSynthesisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (twinSubstrateAuditSynthesis_round_trip x).symm
      (Eq.trans hread (twinSubstrateAuditSynthesis_round_trip y)))

instance twinSubstrateAuditSynthesisBHistCarrier :
    BHistCarrier TwinSubstrateAuditSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := twinSubstrateAuditSynthesisToEventFlow
  fromEventFlow := twinSubstrateAuditSynthesisFromEventFlow

instance twinSubstrateAuditSynthesisChapterTasteGate :
    ChapterTasteGate TwinSubstrateAuditSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change twinSubstrateAuditSynthesisFromEventFlow
        (twinSubstrateAuditSynthesisToEventFlow x) =
      some x
    exact twinSubstrateAuditSynthesis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (twinSubstrateAuditSynthesisToEventFlow_injective heq)

instance twinSubstrateAuditSynthesisFieldFaithful :
    FieldFaithful TwinSubstrateAuditSynthesisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TwinSubstrateAuditSynthesisUp.mk metacic ground frontier transport route provenance name =>
        [metacic, ground, frontier, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk metacic1 ground1 frontier1 transport1 route1 provenance1 name1 =>
        cases y with
        | mk metacic2 ground2 frontier2 transport2 route2 provenance2 name2 =>
            injection h with hMetaCIC t1
            injection t1 with hGround t2
            injection t2 with hFrontier t3
            injection t3 with hTransport t4
            injection t4 with hRoute t5
            injection t5 with hProvenance t6
            injection t6 with hName _
            cases hMetaCIC
            cases hGround
            cases hFrontier
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

theorem TwinSubstrateAuditSynthesisTasteGate_single_carrier_alignment :
    (∀ x : TwinSubstrateAuditSynthesisUp,
      twinSubstrateAuditSynthesisFromEventFlow
          (twinSubstrateAuditSynthesisToEventFlow x) =
        some x) ∧
      (∀ x y : TwinSubstrateAuditSynthesisUp,
        twinSubstrateAuditSynthesisToEventFlow x =
          twinSubstrateAuditSynthesisToEventFlow y →
          x = y) ∧
        (∀ (x : TwinSubstrateAuditSynthesisUp) w m,
          List.Mem w (twinSubstrateAuditSynthesisToEventFlow x) →
            List.Mem m w →
              m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact twinSubstrateAuditSynthesis_round_trip
  · constructor
    · intro x y heq
      exact twinSubstrateAuditSynthesisToEventFlow_injective heq
    · intro x w m hw hm
      exact event_flow_conservativity (S := twinSubstrateAuditSynthesisToEventFlow x) hw hm

end BEDC.Derived.TwinSubstrateAuditSynthesisUp
