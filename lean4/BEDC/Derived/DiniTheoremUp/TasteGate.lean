import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiniTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiniTheoremUp : Type where
  | mk :
      (compact family continuity windows realSeal transport continuation provenance name :
        BHist) ->
        DiniTheoremUp

def diniTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diniTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diniTheoremEncodeBHist h

def diniTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diniTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diniTheoremDecodeBHist tail)

private theorem diniTheoremDecode_encode_bhist :
    forall h : BHist, diniTheoremDecodeBHist (diniTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def diniTheoremToEventFlow : DiniTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiniTheoremUp.mk compact family continuity windows realSeal transport continuation
      provenance name =>
      [BMark.b1 :: BMark.b1 :: BMark.b0 :: BMark.b0 :: [],
        diniTheoremEncodeBHist compact,
        diniTheoremEncodeBHist family,
        diniTheoremEncodeBHist continuity,
        diniTheoremEncodeBHist windows,
        diniTheoremEncodeBHist realSeal,
        diniTheoremEncodeBHist transport,
        diniTheoremEncodeBHist continuation,
        diniTheoremEncodeBHist provenance,
        diniTheoremEncodeBHist name]

def diniTheoremReadRows : EventFlow -> Option DiniTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | compact :: rest1 =>
      match rest1 with
      | family :: rest2 =>
          match rest2 with
          | continuity :: rest3 =>
              match rest3 with
              | windows :: rest4 =>
                  match rest4 with
                  | realSeal :: rest5 =>
                      match rest5 with
                      | transport :: rest6 =>
                          match rest6 with
                          | continuation :: rest7 =>
                              match rest7 with
                              | provenance :: rest8 =>
                                  match rest8 with
                                  | name :: rest9 =>
                                      match rest9 with
                                      | [] =>
                                          some
                                            (DiniTheoremUp.mk
                                              (diniTheoremDecodeBHist compact)
                                              (diniTheoremDecodeBHist family)
                                              (diniTheoremDecodeBHist continuity)
                                              (diniTheoremDecodeBHist windows)
                                              (diniTheoremDecodeBHist realSeal)
                                              (diniTheoremDecodeBHist transport)
                                              (diniTheoremDecodeBHist continuation)
                                              (diniTheoremDecodeBHist provenance)
                                              (diniTheoremDecodeBHist name))
                                      | _ :: _ => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

def diniTheoremFromEventFlow : EventFlow -> Option DiniTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: rows => diniTheoremReadRows rows
  | [] => none

private theorem diniTheorem_round_trip :
    forall x : DiniTheoremUp,
      diniTheoremFromEventFlow (diniTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compact family continuity windows realSeal transport continuation provenance name =>
      change
        some
          (DiniTheoremUp.mk
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist compact))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist family))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist continuity))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist windows))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist realSeal))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist transport))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist continuation))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist provenance))
            (diniTheoremDecodeBHist (diniTheoremEncodeBHist name))) =
          some
            (DiniTheoremUp.mk compact family continuity windows realSeal transport
              continuation provenance name)
      rw [diniTheoremDecode_encode_bhist compact,
        diniTheoremDecode_encode_bhist family,
        diniTheoremDecode_encode_bhist continuity,
        diniTheoremDecode_encode_bhist windows,
        diniTheoremDecode_encode_bhist realSeal,
        diniTheoremDecode_encode_bhist transport,
        diniTheoremDecode_encode_bhist continuation,
        diniTheoremDecode_encode_bhist provenance,
        diniTheoremDecode_encode_bhist name]

private theorem diniTheoremToEventFlow_injective {x y : DiniTheoremUp} :
    diniTheoremToEventFlow x = diniTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diniTheoremFromEventFlow (diniTheoremToEventFlow x) =
        diniTheoremFromEventFlow (diniTheoremToEventFlow y) :=
    congrArg diniTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diniTheorem_round_trip x).symm
      (Eq.trans hread (diniTheorem_round_trip y)))

instance diniTheoremBHistCarrier : BHistCarrier DiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diniTheoremToEventFlow
  fromEventFlow := diniTheoremFromEventFlow

instance diniTheoremChapterTasteGate : ChapterTasteGate DiniTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diniTheoremFromEventFlow (diniTheoremToEventFlow x) = some x
    exact diniTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diniTheoremToEventFlow_injective heq)

theorem DiniTheoremTasteGate_single_carrier_alignment :
    (forall h : BHist, diniTheoremDecodeBHist (diniTheoremEncodeBHist h) = h) /\
      (forall x : DiniTheoremUp,
        diniTheoremFromEventFlow (diniTheoremToEventFlow x) = some x) /\
      (forall {x y : DiniTheoremUp},
        diniTheoremToEventFlow x = diniTheoremToEventFlow y -> x = y) /\
      diniTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diniTheoremDecode_encode_bhist
  · constructor
    · intro x
      change diniTheoremFromEventFlow (diniTheoremToEventFlow x) = some x
      exact diniTheorem_round_trip x
    · constructor
      · intro x y heq
        exact diniTheoremToEventFlow_injective heq
      · rfl

end BEDC.Derived.DiniTheoremUp
