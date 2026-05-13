import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GeneratorFixedPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GeneratorFixedPointUp : Type where
  | mk :
      (generator seed iterate fixedPoint witness route provenance nameCert : BHist) →
      GeneratorFixedPointUp
  deriving DecidableEq

private def generatorFixedPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: generatorFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: generatorFixedPointEncodeBHist h

private def generatorFixedPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (generatorFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (generatorFixedPointDecodeBHist tail)

private theorem generatorFixedPointDecode_encode_bhist :
    ∀ h : BHist, generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem generatorFixedPoint_mk_congr
    {generator generator' seed seed' iterate iterate' fixedPoint fixedPoint'
      witness witness' route route' provenance provenance' nameCert nameCert' : BHist}
    (hGenerator : generator' = generator)
    (hSeed : seed' = seed)
    (hIterate : iterate' = iterate)
    (hFixedPoint : fixedPoint' = fixedPoint)
    (hWitness : witness' = witness)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    GeneratorFixedPointUp.mk generator' seed' iterate' fixedPoint' witness' route'
        provenance' nameCert' =
      GeneratorFixedPointUp.mk generator seed iterate fixedPoint witness route provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGenerator
  cases hSeed
  cases hIterate
  cases hFixedPoint
  cases hWitness
  cases hRoute
  cases hProvenance
  cases hNameCert
  rfl

private def generatorFixedPointToEventFlow : GeneratorFixedPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GeneratorFixedPointUp.mk generator seed iterate fixedPoint witness route provenance
      nameCert =>
      [[BMark.b0],
        generatorFixedPointEncodeBHist generator,
        [BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist seed,
        [BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist iterate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist fixedPoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        generatorFixedPointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        generatorFixedPointEncodeBHist nameCert]

private def generatorFixedPointFromEventFlow : EventFlow → Option GeneratorFixedPointUp
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
              | seed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | iterate :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fixedPoint :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | witness :: rest9 =>
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
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (GeneratorFixedPointUp.mk
                                                                          (generatorFixedPointDecodeBHist generator)
                                                                          (generatorFixedPointDecodeBHist seed)
                                                                          (generatorFixedPointDecodeBHist iterate)
                                                                          (generatorFixedPointDecodeBHist fixedPoint)
                                                                          (generatorFixedPointDecodeBHist witness)
                                                                          (generatorFixedPointDecodeBHist route)
                                                                          (generatorFixedPointDecodeBHist provenance)
                                                                          (generatorFixedPointDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem generatorFixedPoint_round_trip :
    ∀ x : GeneratorFixedPointUp,
      generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generator seed iterate fixedPoint witness route provenance nameCert =>
      change
        some
          (GeneratorFixedPointUp.mk
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist generator))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist seed))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist iterate))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist fixedPoint))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist witness))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist route))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist provenance))
            (generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist nameCert))) =
          some
            (GeneratorFixedPointUp.mk generator seed iterate fixedPoint witness route
              provenance nameCert)
      exact
        congrArg some
          (generatorFixedPoint_mk_congr
            (generatorFixedPointDecode_encode_bhist generator)
            (generatorFixedPointDecode_encode_bhist seed)
            (generatorFixedPointDecode_encode_bhist iterate)
            (generatorFixedPointDecode_encode_bhist fixedPoint)
            (generatorFixedPointDecode_encode_bhist witness)
            (generatorFixedPointDecode_encode_bhist route)
            (generatorFixedPointDecode_encode_bhist provenance)
            (generatorFixedPointDecode_encode_bhist nameCert))

private theorem generatorFixedPointToEventFlow_injective {x y : GeneratorFixedPointUp} :
    generatorFixedPointToEventFlow x = generatorFixedPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) =
        generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow y) :=
    congrArg generatorFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (generatorFixedPoint_round_trip x).symm
      (Eq.trans hread (generatorFixedPoint_round_trip y)))

instance generatorFixedPointBHistCarrier : BHistCarrier GeneratorFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := generatorFixedPointToEventFlow
  fromEventFlow := generatorFixedPointFromEventFlow

instance generatorFixedPointChapterTasteGate : ChapterTasteGate GeneratorFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) = some x
    exact generatorFixedPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (generatorFixedPointToEventFlow_injective heq)

theorem GeneratorFixedPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, generatorFixedPointDecodeBHist (generatorFixedPointEncodeBHist h) = h) ∧
      (∀ x : GeneratorFixedPointUp,
        generatorFixedPointFromEventFlow (generatorFixedPointToEventFlow x) = some x) ∧
        (∀ x y : GeneratorFixedPointUp,
          generatorFixedPointToEventFlow x = generatorFixedPointToEventFlow y → x = y) ∧
          generatorFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact generatorFixedPointDecode_encode_bhist
  · constructor
    · exact generatorFixedPoint_round_trip
    · constructor
      · intro x y heq
        exact generatorFixedPointToEventFlow_injective heq
      · rfl

end BEDC.Derived.GeneratorFixedPointUp
