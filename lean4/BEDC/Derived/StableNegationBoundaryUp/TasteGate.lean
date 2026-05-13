import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StableNegationBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StableNegationBoundaryUp : Type where
  | mk :
      (proposition refutation decision classifier ledger transport route provenance cert : BHist) ->
      StableNegationBoundaryUp
  deriving DecidableEq

def stableNegationBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stableNegationBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stableNegationBoundaryEncodeBHist h

def stableNegationBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stableNegationBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stableNegationBoundaryDecodeBHist tail)

private theorem stableNegationBoundaryDecode_encode_bhist :
    forall h : BHist,
      stableNegationBoundaryDecodeBHist (stableNegationBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stableNegationBoundaryToEventFlow : StableNegationBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StableNegationBoundaryUp.mk proposition refutation decision classifier ledger transport
      route provenance cert =>
      [[BMark.b0],
        stableNegationBoundaryEncodeBHist proposition,
        [BMark.b1, BMark.b0],
        stableNegationBoundaryEncodeBHist refutation,
        [BMark.b1, BMark.b1, BMark.b0],
        stableNegationBoundaryEncodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stableNegationBoundaryEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stableNegationBoundaryEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stableNegationBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        stableNegationBoundaryEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        stableNegationBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        stableNegationBoundaryEncodeBHist cert]

def stableNegationBoundaryFromEventFlow :
    EventFlow -> Option StableNegationBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | proposition :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refutation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | decision :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | ledger :: rest9 =>
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
                                                      | route :: rest13 =>
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
                                                                      | cert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (StableNegationBoundaryUp.mk
                                                                                  (stableNegationBoundaryDecodeBHist proposition)
                                                                                  (stableNegationBoundaryDecodeBHist refutation)
                                                                                  (stableNegationBoundaryDecodeBHist decision)
                                                                                  (stableNegationBoundaryDecodeBHist classifier)
                                                                                  (stableNegationBoundaryDecodeBHist ledger)
                                                                                  (stableNegationBoundaryDecodeBHist transport)
                                                                                  (stableNegationBoundaryDecodeBHist route)
                                                                                  (stableNegationBoundaryDecodeBHist provenance)
                                                                                  (stableNegationBoundaryDecodeBHist cert))
                                                                          | _ :: _ => none

private theorem stableNegationBoundary_round_trip :
    forall x : StableNegationBoundaryUp,
      stableNegationBoundaryFromEventFlow
        (stableNegationBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk proposition refutation decision classifier ledger transport route provenance cert =>
      change
        some
          (StableNegationBoundaryUp.mk
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist proposition))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist refutation))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist decision))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist classifier))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist ledger))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist transport))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist route))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist provenance))
            (stableNegationBoundaryDecodeBHist
              (stableNegationBoundaryEncodeBHist cert))) =
          some
            (StableNegationBoundaryUp.mk proposition refutation decision classifier ledger
              transport route provenance cert)
      rw [stableNegationBoundaryDecode_encode_bhist proposition,
        stableNegationBoundaryDecode_encode_bhist refutation,
        stableNegationBoundaryDecode_encode_bhist decision,
        stableNegationBoundaryDecode_encode_bhist classifier,
        stableNegationBoundaryDecode_encode_bhist ledger,
        stableNegationBoundaryDecode_encode_bhist transport,
        stableNegationBoundaryDecode_encode_bhist route,
        stableNegationBoundaryDecode_encode_bhist provenance,
        stableNegationBoundaryDecode_encode_bhist cert]

private theorem stableNegationBoundaryToEventFlow_injective
    {x y : StableNegationBoundaryUp} :
    stableNegationBoundaryToEventFlow x = stableNegationBoundaryToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stableNegationBoundaryFromEventFlow
          (stableNegationBoundaryToEventFlow x) =
        stableNegationBoundaryFromEventFlow
          (stableNegationBoundaryToEventFlow y) :=
    congrArg stableNegationBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stableNegationBoundary_round_trip x).symm
      (Eq.trans hread (stableNegationBoundary_round_trip y)))

instance stableNegationBoundaryBHistCarrier : BHistCarrier StableNegationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stableNegationBoundaryToEventFlow
  fromEventFlow := stableNegationBoundaryFromEventFlow

instance stableNegationBoundaryChapterTasteGate :
    ChapterTasteGate StableNegationBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stableNegationBoundaryFromEventFlow
      (stableNegationBoundaryToEventFlow x) = some x
    exact stableNegationBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stableNegationBoundaryToEventFlow_injective heq)

theorem StableNegationBoundaryTasteGate_single_carrier_alignment :
    (forall h : BHist,
      stableNegationBoundaryDecodeBHist
        (stableNegationBoundaryEncodeBHist h) = h) ∧
      (forall x : StableNegationBoundaryUp,
        stableNegationBoundaryFromEventFlow
          (stableNegationBoundaryToEventFlow x) = some x) ∧
        (forall x y : StableNegationBoundaryUp,
          stableNegationBoundaryToEventFlow x =
            stableNegationBoundaryToEventFlow y -> x = y) ∧
          stableNegationBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact stableNegationBoundaryDecode_encode_bhist
  · constructor
    · exact stableNegationBoundary_round_trip
    · constructor
      · intro x y heq
        exact stableNegationBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.StableNegationBoundaryUp
