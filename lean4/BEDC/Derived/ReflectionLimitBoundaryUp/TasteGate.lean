import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReflectionLimitBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReflectionLimitBoundaryUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (ground metaRow truth transport continuation provenance name : BHist) →
      ReflectionLimitBoundaryUp
  deriving DecidableEq

def reflectionLimitBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reflectionLimitBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reflectionLimitBoundaryEncodeBHist h

def reflectionLimitBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reflectionLimitBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reflectionLimitBoundaryDecodeBHist tail)

private theorem ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, reflectionLimitBoundaryDecodeBHist
      (reflectionLimitBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem ReflectionLimitBoundaryTasteGate_single_carrier_alignment_mk_congr
    {ground ground' metaRow metaRow' truth truth' transport transport' continuation continuation'
      provenance provenance' name name' : BHist}
    (hGround : ground' = ground)
    (hMeta : metaRow' = metaRow)
    (hTruth : truth' = truth)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    ReflectionLimitBoundaryUp.mk ground' metaRow' truth' transport' continuation' provenance'
        name' =
      ReflectionLimitBoundaryUp.mk ground metaRow truth transport continuation provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGround
  cases hMeta
  cases hTruth
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hName
  rfl

def reflectionLimitBoundaryToEventFlow : ReflectionLimitBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectionLimitBoundaryUp.mk ground metaRow truth transport continuation provenance name =>
      [[BMark.b0],
        reflectionLimitBoundaryEncodeBHist ground,
        [BMark.b1, BMark.b0],
        reflectionLimitBoundaryEncodeBHist metaRow,
        [BMark.b1, BMark.b1, BMark.b0],
        reflectionLimitBoundaryEncodeBHist truth,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionLimitBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionLimitBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionLimitBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectionLimitBoundaryEncodeBHist name]

def reflectionLimitBoundaryFromEventFlow : EventFlow → Option ReflectionLimitBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | ground :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | metaRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | truth :: rest5 =>
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
                                      | continuation :: rest9 =>
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
                                                                (ReflectionLimitBoundaryUp.mk
                                                                  (reflectionLimitBoundaryDecodeBHist
                                                                    ground)
                                                                  (reflectionLimitBoundaryDecodeBHist
                                                                    metaRow)
                                                                  (reflectionLimitBoundaryDecodeBHist
                                                                    truth)
                                                                  (reflectionLimitBoundaryDecodeBHist
                                                                    transport)
                                                                  (reflectionLimitBoundaryDecodeBHist
                                                                    continuation)
                                                                  (reflectionLimitBoundaryDecodeBHist
                                                                    provenance)
                                                                  (reflectionLimitBoundaryDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem ReflectionLimitBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ReflectionLimitBoundaryUp,
      reflectionLimitBoundaryFromEventFlow (reflectionLimitBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ground metaRow truth transport continuation provenance name =>
      change
        some
          (ReflectionLimitBoundaryUp.mk
            (reflectionLimitBoundaryDecodeBHist
              (reflectionLimitBoundaryEncodeBHist ground))
            (reflectionLimitBoundaryDecodeBHist
              (reflectionLimitBoundaryEncodeBHist metaRow))
            (reflectionLimitBoundaryDecodeBHist
              (reflectionLimitBoundaryEncodeBHist truth))
            (reflectionLimitBoundaryDecodeBHist
              (reflectionLimitBoundaryEncodeBHist transport))
            (reflectionLimitBoundaryDecodeBHist
              (reflectionLimitBoundaryEncodeBHist continuation))
            (reflectionLimitBoundaryDecodeBHist
              (reflectionLimitBoundaryEncodeBHist provenance))
            (reflectionLimitBoundaryDecodeBHist
              (reflectionLimitBoundaryEncodeBHist name))) =
          some
            (ReflectionLimitBoundaryUp.mk ground metaRow truth transport continuation provenance
              name)
      exact
        congrArg some
          (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_mk_congr
            (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode ground)
            (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode metaRow)
            (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode truth)
            (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode transport)
            (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode
              continuation)
            (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode
              provenance)
            (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode name))

private theorem ReflectionLimitBoundaryTasteGate_single_carrier_alignment_injective
    {x y : ReflectionLimitBoundaryUp} :
    reflectionLimitBoundaryToEventFlow x = reflectionLimitBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reflectionLimitBoundaryFromEventFlow (reflectionLimitBoundaryToEventFlow x) =
        reflectionLimitBoundaryFromEventFlow (reflectionLimitBoundaryToEventFlow y) :=
    congrArg reflectionLimitBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_round_trip y)))

instance reflectionLimitBoundaryBHistCarrier : BHistCarrier ReflectionLimitBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reflectionLimitBoundaryToEventFlow
  fromEventFlow := reflectionLimitBoundaryFromEventFlow

instance reflectionLimitBoundaryChapterTasteGate : ChapterTasteGate ReflectionLimitBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reflectionLimitBoundaryFromEventFlow (reflectionLimitBoundaryToEventFlow x) =
      some x
    exact ReflectionLimitBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ReflectionLimitBoundaryTasteGate_single_carrier_alignment_injective heq)

theorem ReflectionLimitBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      reflectionLimitBoundaryDecodeBHist (reflectionLimitBoundaryEncodeBHist h) = h) /\
      (forall x : ReflectionLimitBoundaryUp,
        reflectionLimitBoundaryFromEventFlow (reflectionLimitBoundaryToEventFlow x) =
          some x) /\
        (forall x y : ReflectionLimitBoundaryUp,
          reflectionLimitBoundaryToEventFlow x = reflectionLimitBoundaryToEventFlow y ->
            x = y) /\
          reflectionLimitBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ReflectionLimitBoundaryTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ReflectionLimitBoundaryTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact ReflectionLimitBoundaryTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.ReflectionLimitBoundaryUp
