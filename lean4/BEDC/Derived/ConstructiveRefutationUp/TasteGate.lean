import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveRefutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveRefutationUp : Type where
  | mk :
      (assumption route contradiction decision scope transport provenance name : BHist) ->
      ConstructiveRefutationUp
  deriving DecidableEq

def constructiveRefutationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveRefutationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveRefutationEncodeBHist h

def constructiveRefutationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveRefutationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveRefutationDecodeBHist tail)

private theorem constructiveRefutationDecode_encode_bhist :
    forall h : BHist,
      constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def constructiveRefutationToEventFlow : ConstructiveRefutationUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveRefutationUp.mk assumption route contradiction decision scope transport
      provenance name =>
      [[BMark.b0],
        constructiveRefutationEncodeBHist assumption,
        [BMark.b1, BMark.b0],
        constructiveRefutationEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b0],
        constructiveRefutationEncodeBHist contradiction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveRefutationEncodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveRefutationEncodeBHist scope,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveRefutationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        constructiveRefutationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        constructiveRefutationEncodeBHist name]

def constructiveRefutationFromEventFlow : EventFlow -> Option ConstructiveRefutationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | assumption :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | route :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | contradiction :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | decision :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | scope :: rest9 =>
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
                                                                        (ConstructiveRefutationUp.mk
                                                                          (constructiveRefutationDecodeBHist
                                                                            assumption)
                                                                          (constructiveRefutationDecodeBHist
                                                                            route)
                                                                          (constructiveRefutationDecodeBHist
                                                                            contradiction)
                                                                          (constructiveRefutationDecodeBHist
                                                                            decision)
                                                                          (constructiveRefutationDecodeBHist
                                                                            scope)
                                                                          (constructiveRefutationDecodeBHist
                                                                            transport)
                                                                          (constructiveRefutationDecodeBHist
                                                                            provenance)
                                                                          (constructiveRefutationDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem constructiveRefutation_round_trip :
    forall x : ConstructiveRefutationUp,
      constructiveRefutationFromEventFlow (constructiveRefutationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk assumption route contradiction decision scope transport provenance name =>
      change
        some
          (ConstructiveRefutationUp.mk
            (constructiveRefutationDecodeBHist
              (constructiveRefutationEncodeBHist assumption))
            (constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist route))
            (constructiveRefutationDecodeBHist
              (constructiveRefutationEncodeBHist contradiction))
            (constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist decision))
            (constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist scope))
            (constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist transport))
            (constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist provenance))
            (constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist name))) =
          some
            (ConstructiveRefutationUp.mk assumption route contradiction decision scope transport
              provenance name)
      rw [constructiveRefutationDecode_encode_bhist assumption,
        constructiveRefutationDecode_encode_bhist route,
        constructiveRefutationDecode_encode_bhist contradiction,
        constructiveRefutationDecode_encode_bhist decision,
        constructiveRefutationDecode_encode_bhist scope,
        constructiveRefutationDecode_encode_bhist transport,
        constructiveRefutationDecode_encode_bhist provenance,
        constructiveRefutationDecode_encode_bhist name]

private theorem constructiveRefutationToEventFlow_injective {x y : ConstructiveRefutationUp} :
    constructiveRefutationToEventFlow x = constructiveRefutationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveRefutationFromEventFlow (constructiveRefutationToEventFlow x) =
        constructiveRefutationFromEventFlow (constructiveRefutationToEventFlow y) :=
    congrArg constructiveRefutationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (constructiveRefutation_round_trip x).symm
      (Eq.trans hread (constructiveRefutation_round_trip y)))

instance constructiveRefutationBHistCarrier : BHistCarrier ConstructiveRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveRefutationToEventFlow
  fromEventFlow := constructiveRefutationFromEventFlow

instance constructiveRefutationChapterTasteGate : ChapterTasteGate ConstructiveRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveRefutationFromEventFlow (constructiveRefutationToEventFlow x) = some x
    exact constructiveRefutation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (constructiveRefutationToEventFlow_injective heq)

theorem ConstructiveRefutationTasteGate_single_carrier_alignment :
    (forall h : BHist,
      constructiveRefutationDecodeBHist (constructiveRefutationEncodeBHist h) = h) /\
      (forall x : ConstructiveRefutationUp,
        constructiveRefutationFromEventFlow (constructiveRefutationToEventFlow x) = some x) /\
        (forall x y : ConstructiveRefutationUp,
          constructiveRefutationToEventFlow x = constructiveRefutationToEventFlow y -> x = y) /\
          constructiveRefutationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact constructiveRefutationDecode_encode_bhist
  · constructor
    · exact constructiveRefutation_round_trip
    · constructor
      · intro x y heq
        exact constructiveRefutationToEventFlow_injective heq
      · rfl

end BEDC.Derived.ConstructiveRefutationUp
