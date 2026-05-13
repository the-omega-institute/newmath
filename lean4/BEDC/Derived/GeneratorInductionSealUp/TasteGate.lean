import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneratorInductionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeneratorInductionSealUp : Type where
  | mk :
      (generator witness classifier residue transport routes provenance nameCert : BHist) ->
      GeneratorInductionSealUp
  deriving DecidableEq

def generatorInductionSealEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: generatorInductionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: generatorInductionSealEncodeBHist h

def generatorInductionSealDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (generatorInductionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (generatorInductionSealDecodeBHist tail)

private theorem generatorInductionSealDecode_encode_bhist :
    forall h : BHist,
      generatorInductionSealDecodeBHist (generatorInductionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def generatorInductionSealToEventFlow : GeneratorInductionSealUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GeneratorInductionSealUp.mk generator witness classifier residue transport routes provenance
      nameCert =>
      [[BMark.b0],
        generatorInductionSealEncodeBHist generator,
        [BMark.b1, BMark.b0],
        generatorInductionSealEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b0],
        generatorInductionSealEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorInductionSealEncodeBHist residue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorInductionSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorInductionSealEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorInductionSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        generatorInductionSealEncodeBHist nameCert]

def generatorInductionSealFromEventFlow : EventFlow -> Option GeneratorInductionSealUp
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
              | witness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | classifier :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | residue :: rest7 =>
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
                                              | routes :: rest11 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (GeneratorInductionSealUp.mk
                                                                          (generatorInductionSealDecodeBHist
                                                                            generator)
                                                                          (generatorInductionSealDecodeBHist
                                                                            witness)
                                                                          (generatorInductionSealDecodeBHist
                                                                            classifier)
                                                                          (generatorInductionSealDecodeBHist
                                                                            residue)
                                                                          (generatorInductionSealDecodeBHist
                                                                            transport)
                                                                          (generatorInductionSealDecodeBHist
                                                                            routes)
                                                                          (generatorInductionSealDecodeBHist
                                                                            provenance)
                                                                          (generatorInductionSealDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem generatorInductionSeal_round_trip :
    forall x : GeneratorInductionSealUp,
      generatorInductionSealFromEventFlow (generatorInductionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generator witness classifier residue transport routes provenance nameCert =>
      change
        some
          (GeneratorInductionSealUp.mk
            (generatorInductionSealDecodeBHist
              (generatorInductionSealEncodeBHist generator))
            (generatorInductionSealDecodeBHist (generatorInductionSealEncodeBHist witness))
            (generatorInductionSealDecodeBHist
              (generatorInductionSealEncodeBHist classifier))
            (generatorInductionSealDecodeBHist (generatorInductionSealEncodeBHist residue))
            (generatorInductionSealDecodeBHist
              (generatorInductionSealEncodeBHist transport))
            (generatorInductionSealDecodeBHist (generatorInductionSealEncodeBHist routes))
            (generatorInductionSealDecodeBHist
              (generatorInductionSealEncodeBHist provenance))
            (generatorInductionSealDecodeBHist
              (generatorInductionSealEncodeBHist nameCert))) =
          some
            (GeneratorInductionSealUp.mk generator witness classifier residue transport routes
              provenance nameCert)
      rw [generatorInductionSealDecode_encode_bhist generator,
        generatorInductionSealDecode_encode_bhist witness,
        generatorInductionSealDecode_encode_bhist classifier,
        generatorInductionSealDecode_encode_bhist residue,
        generatorInductionSealDecode_encode_bhist transport,
        generatorInductionSealDecode_encode_bhist routes,
        generatorInductionSealDecode_encode_bhist provenance,
        generatorInductionSealDecode_encode_bhist nameCert]

private theorem generatorInductionSealToEventFlow_injective {x y : GeneratorInductionSealUp} :
    generatorInductionSealToEventFlow x = generatorInductionSealToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      generatorInductionSealFromEventFlow (generatorInductionSealToEventFlow x) =
        generatorInductionSealFromEventFlow (generatorInductionSealToEventFlow y) :=
    congrArg generatorInductionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (generatorInductionSeal_round_trip x).symm
      (Eq.trans hread (generatorInductionSeal_round_trip y)))

instance generatorInductionSealBHistCarrier : BHistCarrier GeneratorInductionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := generatorInductionSealToEventFlow
  fromEventFlow := generatorInductionSealFromEventFlow

instance generatorInductionSealChapterTasteGate :
    ChapterTasteGate GeneratorInductionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change generatorInductionSealFromEventFlow (generatorInductionSealToEventFlow x) = some x
    exact generatorInductionSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (generatorInductionSealToEventFlow_injective heq)

theorem GeneratorInductionSealTasteGate_single_carrier_alignment :
    (forall h : BHist,
      generatorInductionSealDecodeBHist (generatorInductionSealEncodeBHist h) = h) /\
      (forall x : GeneratorInductionSealUp,
        generatorInductionSealFromEventFlow (generatorInductionSealToEventFlow x) = some x) /\
        (forall x y : GeneratorInductionSealUp,
          generatorInductionSealToEventFlow x = generatorInductionSealToEventFlow y -> x = y) /\
          generatorInductionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact generatorInductionSealDecode_encode_bhist
  · constructor
    · exact generatorInductionSeal_round_trip
    · constructor
      · intro x y heq
        exact generatorInductionSealToEventFlow_injective heq
      · rfl

end BEDC.Derived.GeneratorInductionSealUp
