import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteIntersectionCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteIntersectionCompactnessUp : Type where
  | mk :
      (finiteIntersection compactMetric closedIntervalWindow finiteEpsilonNet realSeal
        transport replay provenance name : BHist) →
      FiniteIntersectionCompactnessUp
  deriving DecidableEq

def finiteIntersectionCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteIntersectionCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteIntersectionCompactnessEncodeBHist h

def finiteIntersectionCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteIntersectionCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteIntersectionCompactnessDecodeBHist tail)

private theorem finiteIntersectionCompactnessDecode_encode_bhist :
    ∀ h : BHist,
      finiteIntersectionCompactnessDecodeBHist
          (finiteIntersectionCompactnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteIntersectionCompactnessToEventFlow :
    FiniteIntersectionCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteIntersectionCompactnessUp.mk finiteIntersection compactMetric closedIntervalWindow
      finiteEpsilonNet realSeal transport replay provenance name =>
      [[BMark.b0],
        finiteIntersectionCompactnessEncodeBHist finiteIntersection,
        [BMark.b1, BMark.b0],
        finiteIntersectionCompactnessEncodeBHist compactMetric,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteIntersectionCompactnessEncodeBHist closedIntervalWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteIntersectionCompactnessEncodeBHist finiteEpsilonNet,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteIntersectionCompactnessEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteIntersectionCompactnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteIntersectionCompactnessEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteIntersectionCompactnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteIntersectionCompactnessEncodeBHist name]

def finiteIntersectionCompactnessFromEventFlow :
    EventFlow → Option FiniteIntersectionCompactnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | finiteIntersection :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | compactMetric :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | closedIntervalWindow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | finiteEpsilonNet :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | realSeal :: rest9 =>
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
                                                      | replay :: rest13 =>
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
                                                                                (FiniteIntersectionCompactnessUp.mk
                                                                                  (finiteIntersectionCompactnessDecodeBHist finiteIntersection)
                                                                                  (finiteIntersectionCompactnessDecodeBHist compactMetric)
                                                                                  (finiteIntersectionCompactnessDecodeBHist closedIntervalWindow)
                                                                                  (finiteIntersectionCompactnessDecodeBHist finiteEpsilonNet)
                                                                                  (finiteIntersectionCompactnessDecodeBHist realSeal)
                                                                                  (finiteIntersectionCompactnessDecodeBHist transport)
                                                                                  (finiteIntersectionCompactnessDecodeBHist replay)
                                                                                  (finiteIntersectionCompactnessDecodeBHist provenance)
                                                                                  (finiteIntersectionCompactnessDecodeBHist name))
                                                                          | _ :: _ => none

private theorem finiteIntersectionCompactness_round_trip :
    ∀ x : FiniteIntersectionCompactnessUp,
      finiteIntersectionCompactnessFromEventFlow
          (finiteIntersectionCompactnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk finiteIntersection compactMetric closedIntervalWindow finiteEpsilonNet realSeal
      transport replay provenance name =>
      change
        some
          (FiniteIntersectionCompactnessUp.mk
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist finiteIntersection))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist compactMetric))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist closedIntervalWindow))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist finiteEpsilonNet))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist realSeal))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist transport))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist replay))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist provenance))
            (finiteIntersectionCompactnessDecodeBHist
              (finiteIntersectionCompactnessEncodeBHist name))) =
          some
            (FiniteIntersectionCompactnessUp.mk finiteIntersection compactMetric
              closedIntervalWindow finiteEpsilonNet realSeal transport replay provenance name)
      rw [finiteIntersectionCompactnessDecode_encode_bhist finiteIntersection,
        finiteIntersectionCompactnessDecode_encode_bhist compactMetric,
        finiteIntersectionCompactnessDecode_encode_bhist closedIntervalWindow,
        finiteIntersectionCompactnessDecode_encode_bhist finiteEpsilonNet,
        finiteIntersectionCompactnessDecode_encode_bhist realSeal,
        finiteIntersectionCompactnessDecode_encode_bhist transport,
        finiteIntersectionCompactnessDecode_encode_bhist replay,
        finiteIntersectionCompactnessDecode_encode_bhist provenance,
        finiteIntersectionCompactnessDecode_encode_bhist name]

private theorem finiteIntersectionCompactnessToEventFlow_injective
    {x y : FiniteIntersectionCompactnessUp} :
    finiteIntersectionCompactnessToEventFlow x =
        finiteIntersectionCompactnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteIntersectionCompactnessFromEventFlow
          (finiteIntersectionCompactnessToEventFlow x) =
        finiteIntersectionCompactnessFromEventFlow
          (finiteIntersectionCompactnessToEventFlow y) :=
    congrArg finiteIntersectionCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteIntersectionCompactness_round_trip x).symm
      (Eq.trans hread (finiteIntersectionCompactness_round_trip y)))

instance finiteIntersectionCompactnessBHistCarrier :
    BHistCarrier FiniteIntersectionCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteIntersectionCompactnessToEventFlow
  fromEventFlow := finiteIntersectionCompactnessFromEventFlow

instance finiteIntersectionCompactnessChapterTasteGate :
    ChapterTasteGate FiniteIntersectionCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteIntersectionCompactnessFromEventFlow
          (finiteIntersectionCompactnessToEventFlow x) =
        some x
    exact finiteIntersectionCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteIntersectionCompactnessToEventFlow_injective heq)

theorem FiniteIntersectionCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteIntersectionCompactnessDecodeBHist
          (finiteIntersectionCompactnessEncodeBHist h) =
        h) ∧
      (∀ x : FiniteIntersectionCompactnessUp,
        finiteIntersectionCompactnessFromEventFlow
            (finiteIntersectionCompactnessToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteIntersectionCompactnessUp,
          finiteIntersectionCompactnessToEventFlow x =
              finiteIntersectionCompactnessToEventFlow y →
            x = y) ∧
          finiteIntersectionCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteIntersectionCompactnessDecode_encode_bhist
  · constructor
    · exact finiteIntersectionCompactness_round_trip
    · constructor
      · intro x y heq
        exact finiteIntersectionCompactnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.FiniteIntersectionCompactnessUp
