import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DecidableRefutationBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DecidableRefutationBoundaryUp : Type where
  | mk :
      (assumption decision falsity transport continuation provenance name : BHist) ->
      DecidableRefutationBoundaryUp
  deriving DecidableEq

def decidableRefutationBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decidableRefutationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decidableRefutationBoundaryEncodeBHist h

def decidableRefutationBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decidableRefutationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decidableRefutationBoundaryDecodeBHist tail)

private theorem decidableRefutationBoundaryDecode_encode_bhist :
    forall h : BHist,
      decidableRefutationBoundaryDecodeBHist
        (decidableRefutationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def decidableRefutationBoundaryToEventFlow : DecidableRefutationBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DecidableRefutationBoundaryUp.mk assumption decision falsity transport continuation
      provenance name =>
      [[BMark.b0],
        decidableRefutationBoundaryEncodeBHist assumption,
        [BMark.b1, BMark.b0],
        decidableRefutationBoundaryEncodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationBoundaryEncodeBHist falsity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        decidableRefutationBoundaryEncodeBHist name]

def decidableRefutationBoundaryFromEventFlow :
    EventFlow -> Option DecidableRefutationBoundaryUp
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
              | decision :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | falsity :: rest5 =>
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
                                                                (DecidableRefutationBoundaryUp.mk
                                                                  (decidableRefutationBoundaryDecodeBHist
                                                                    assumption)
                                                                  (decidableRefutationBoundaryDecodeBHist
                                                                    decision)
                                                                  (decidableRefutationBoundaryDecodeBHist
                                                                    falsity)
                                                                  (decidableRefutationBoundaryDecodeBHist
                                                                    transport)
                                                                  (decidableRefutationBoundaryDecodeBHist
                                                                    continuation)
                                                                  (decidableRefutationBoundaryDecodeBHist
                                                                    provenance)
                                                                  (decidableRefutationBoundaryDecodeBHist
                                                                    name))
                                                          | _ :: _ => none

private theorem decidableRefutationBoundary_round_trip :
    forall x : DecidableRefutationBoundaryUp,
      decidableRefutationBoundaryFromEventFlow
        (decidableRefutationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk assumption decision falsity transport continuation provenance name =>
      change
        some
          (DecidableRefutationBoundaryUp.mk
            (decidableRefutationBoundaryDecodeBHist
              (decidableRefutationBoundaryEncodeBHist assumption))
            (decidableRefutationBoundaryDecodeBHist
              (decidableRefutationBoundaryEncodeBHist decision))
            (decidableRefutationBoundaryDecodeBHist
              (decidableRefutationBoundaryEncodeBHist falsity))
            (decidableRefutationBoundaryDecodeBHist
              (decidableRefutationBoundaryEncodeBHist transport))
            (decidableRefutationBoundaryDecodeBHist
              (decidableRefutationBoundaryEncodeBHist continuation))
            (decidableRefutationBoundaryDecodeBHist
              (decidableRefutationBoundaryEncodeBHist provenance))
            (decidableRefutationBoundaryDecodeBHist
              (decidableRefutationBoundaryEncodeBHist name))) =
          some
            (DecidableRefutationBoundaryUp.mk assumption decision falsity transport
              continuation provenance name)
      rw [decidableRefutationBoundaryDecode_encode_bhist assumption,
        decidableRefutationBoundaryDecode_encode_bhist decision,
        decidableRefutationBoundaryDecode_encode_bhist falsity,
        decidableRefutationBoundaryDecode_encode_bhist transport,
        decidableRefutationBoundaryDecode_encode_bhist continuation,
        decidableRefutationBoundaryDecode_encode_bhist provenance,
        decidableRefutationBoundaryDecode_encode_bhist name]

private theorem decidableRefutationBoundaryToEventFlow_injective
    {x y : DecidableRefutationBoundaryUp} :
    decidableRefutationBoundaryToEventFlow x = decidableRefutationBoundaryToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      decidableRefutationBoundaryFromEventFlow
          (decidableRefutationBoundaryToEventFlow x) =
        decidableRefutationBoundaryFromEventFlow
          (decidableRefutationBoundaryToEventFlow y) :=
    congrArg decidableRefutationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (decidableRefutationBoundary_round_trip x).symm
      (Eq.trans hread (decidableRefutationBoundary_round_trip y)))

instance decidableRefutationBoundaryBHistCarrier :
    BHistCarrier DecidableRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := decidableRefutationBoundaryToEventFlow
  fromEventFlow := decidableRefutationBoundaryFromEventFlow

instance decidableRefutationBoundaryChapterTasteGate :
    ChapterTasteGate DecidableRefutationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      decidableRefutationBoundaryFromEventFlow
        (decidableRefutationBoundaryToEventFlow x) = some x
    exact decidableRefutationBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (decidableRefutationBoundaryToEventFlow_injective heq)

theorem DecidableRefutationBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      decidableRefutationBoundaryDecodeBHist
        (decidableRefutationBoundaryEncodeBHist h) = h) /\
      (forall x : DecidableRefutationBoundaryUp,
        decidableRefutationBoundaryFromEventFlow
          (decidableRefutationBoundaryToEventFlow x) = some x) /\
        (forall x y : DecidableRefutationBoundaryUp,
          decidableRefutationBoundaryToEventFlow x =
            decidableRefutationBoundaryToEventFlow y -> x = y) /\
          decidableRefutationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact decidableRefutationBoundaryDecode_encode_bhist
  · constructor
    · exact decidableRefutationBoundary_round_trip
    · constructor
      · intro x y heq
        exact decidableRefutationBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.DecidableRefutationBoundaryUp
