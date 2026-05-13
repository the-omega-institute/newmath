import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingDiagonalUp : Type where
  | mk :
      (program input selfRef fixed diagonal transport continuation provenance name : BHist) ->
        HaltingDiagonalUp
  deriving DecidableEq

def haltingDiagonalEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingDiagonalEncodeBHist h

def haltingDiagonalDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingDiagonalDecodeBHist tail)

private theorem haltingDiagonalDecode_encode_bhist :
    forall h : BHist, haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def haltingDiagonalToEventFlow : HaltingDiagonalUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingDiagonalUp.mk program input selfRef fixed diagonal transport continuation
      provenance name =>
      [[BMark.b0],
        haltingDiagonalEncodeBHist program,
        [BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist input,
        [BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist selfRef,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist fixed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist diagonal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        haltingDiagonalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        haltingDiagonalEncodeBHist name]

def haltingDiagonalFromEventFlow : EventFlow -> Option HaltingDiagonalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | program :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | input :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | selfRef :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fixed :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | diagonal :: rest9 =>
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
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (HaltingDiagonalUp.mk
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    program)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    input)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    selfRef)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    fixed)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    diagonal)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    transport)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    continuation)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    provenance)
                                                                                  (haltingDiagonalDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem haltingDiagonal_round_trip :
    forall x : HaltingDiagonalUp,
      haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk program input selfRef fixed diagonal transport continuation provenance name =>
      change
        some
          (HaltingDiagonalUp.mk
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist program))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist input))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist selfRef))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist fixed))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist diagonal))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist transport))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist continuation))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist provenance))
            (haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist name))) =
          some
            (HaltingDiagonalUp.mk program input selfRef fixed diagonal transport
              continuation provenance name)
      rw [haltingDiagonalDecode_encode_bhist program, haltingDiagonalDecode_encode_bhist input,
        haltingDiagonalDecode_encode_bhist selfRef, haltingDiagonalDecode_encode_bhist fixed,
        haltingDiagonalDecode_encode_bhist diagonal, haltingDiagonalDecode_encode_bhist transport,
        haltingDiagonalDecode_encode_bhist continuation,
        haltingDiagonalDecode_encode_bhist provenance, haltingDiagonalDecode_encode_bhist name]

private theorem haltingDiagonalToEventFlow_injective {x y : HaltingDiagonalUp} :
    haltingDiagonalToEventFlow x = haltingDiagonalToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) =
        haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow y) :=
    congrArg haltingDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (haltingDiagonal_round_trip x).symm
      (Eq.trans hread (haltingDiagonal_round_trip y)))

instance haltingDiagonalBHistCarrier : BHistCarrier HaltingDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingDiagonalToEventFlow
  fromEventFlow := haltingDiagonalFromEventFlow

instance haltingDiagonalChapterTasteGate : ChapterTasteGate HaltingDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) = some x
    exact haltingDiagonal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (haltingDiagonalToEventFlow_injective heq)

theorem HaltingDiagonalTasteGate_single_carrier_alignment :
    (forall h : BHist, haltingDiagonalDecodeBHist (haltingDiagonalEncodeBHist h) = h) /\
      (forall x : HaltingDiagonalUp,
        haltingDiagonalFromEventFlow (haltingDiagonalToEventFlow x) = some x) /\
        (forall x y : HaltingDiagonalUp,
          haltingDiagonalToEventFlow x = haltingDiagonalToEventFlow y -> x = y) /\
          haltingDiagonalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact haltingDiagonalDecode_encode_bhist
  · constructor
    · exact haltingDiagonal_round_trip
    · constructor
      · intro x y heq
        exact haltingDiagonalToEventFlow_injective heq
      · rfl

end BEDC.Derived.HaltingDiagonalUp
