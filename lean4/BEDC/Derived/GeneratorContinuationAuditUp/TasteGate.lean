import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneratorContinuationAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeneratorContinuationAuditUp : Type where
  | mk :
      (generator continuation witness gap transport route provenance name : BHist) →
        GeneratorContinuationAuditUp
  deriving DecidableEq

def generatorContinuationAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: generatorContinuationAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: generatorContinuationAuditEncodeBHist h

def generatorContinuationAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (generatorContinuationAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (generatorContinuationAuditDecodeBHist tail)

private theorem generatorContinuationAuditDecode_encode_bhist :
    ∀ h : BHist,
      generatorContinuationAuditDecodeBHist
        (generatorContinuationAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def generatorContinuationAuditToEventFlow : GeneratorContinuationAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GeneratorContinuationAuditUp.mk generator continuation witness gap transport route
      provenance name =>
      [[BMark.b0],
        generatorContinuationAuditEncodeBHist generator,
        [BMark.b1, BMark.b0],
        generatorContinuationAuditEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b0],
        generatorContinuationAuditEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorContinuationAuditEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorContinuationAuditEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorContinuationAuditEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorContinuationAuditEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        generatorContinuationAuditEncodeBHist name]

def generatorContinuationAuditFromEventFlow :
    EventFlow → Option GeneratorContinuationAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generator :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | continuation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | witness :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gap :: rest7 =>
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
                                                                        (GeneratorContinuationAuditUp.mk
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            generator)
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            continuation)
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            witness)
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            gap)
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            transport)
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            route)
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            provenance)
                                                                          (generatorContinuationAuditDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem generatorContinuationAudit_round_trip :
    ∀ x : GeneratorContinuationAuditUp,
      generatorContinuationAuditFromEventFlow
        (generatorContinuationAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generator continuation witness gap transport route provenance name =>
      change
        some
          (GeneratorContinuationAuditUp.mk
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist generator))
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist continuation))
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist witness))
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist gap))
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist transport))
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist route))
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist provenance))
            (generatorContinuationAuditDecodeBHist
              (generatorContinuationAuditEncodeBHist name))) =
          some
            (GeneratorContinuationAuditUp.mk generator continuation witness gap transport
              route provenance name)
      rw [generatorContinuationAuditDecode_encode_bhist generator,
        generatorContinuationAuditDecode_encode_bhist continuation,
        generatorContinuationAuditDecode_encode_bhist witness,
        generatorContinuationAuditDecode_encode_bhist gap,
        generatorContinuationAuditDecode_encode_bhist transport,
        generatorContinuationAuditDecode_encode_bhist route,
        generatorContinuationAuditDecode_encode_bhist provenance,
        generatorContinuationAuditDecode_encode_bhist name]

private theorem generatorContinuationAuditToEventFlow_injective
    {x y : GeneratorContinuationAuditUp} :
    generatorContinuationAuditToEventFlow x = generatorContinuationAuditToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      generatorContinuationAuditFromEventFlow (generatorContinuationAuditToEventFlow x) =
        generatorContinuationAuditFromEventFlow (generatorContinuationAuditToEventFlow y) :=
    congrArg generatorContinuationAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (generatorContinuationAudit_round_trip x).symm
      (Eq.trans hread (generatorContinuationAudit_round_trip y)))

instance generatorContinuationAuditBHistCarrier :
    BHistCarrier GeneratorContinuationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := generatorContinuationAuditToEventFlow
  fromEventFlow := generatorContinuationAuditFromEventFlow

instance generatorContinuationAuditChapterTasteGate :
    ChapterTasteGate GeneratorContinuationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      generatorContinuationAuditFromEventFlow
        (generatorContinuationAuditToEventFlow x) = some x
    exact generatorContinuationAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (generatorContinuationAuditToEventFlow_injective heq)

theorem GeneratorContinuationAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      generatorContinuationAuditDecodeBHist
        (generatorContinuationAuditEncodeBHist h) = h) ∧
      (∀ x : GeneratorContinuationAuditUp,
        generatorContinuationAuditFromEventFlow
          (generatorContinuationAuditToEventFlow x) = some x) ∧
        (∀ x y : GeneratorContinuationAuditUp,
          generatorContinuationAuditToEventFlow x =
            generatorContinuationAuditToEventFlow y -> x = y) ∧
          generatorContinuationAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact generatorContinuationAuditDecode_encode_bhist
  · constructor
    · exact generatorContinuationAudit_round_trip
    · constructor
      · intro x y heq
        exact generatorContinuationAuditToEventFlow_injective heq
      · rfl

end BEDC.Derived.GeneratorContinuationAuditUp
