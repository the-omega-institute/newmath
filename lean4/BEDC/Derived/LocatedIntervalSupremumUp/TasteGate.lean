import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalSupremumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalSupremumUp : Type where
  | mk :
      (intervalSource upperBound lowerApprox bisection window readback realSeal
        transport replay provenance name : BHist) →
      LocatedIntervalSupremumUp
  deriving DecidableEq

def locatedIntervalSupremumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalSupremumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalSupremumEncodeBHist h

def locatedIntervalSupremumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalSupremumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalSupremumDecodeBHist tail)

private theorem locatedIntervalSupremumDecode_encode_bhist :
    ∀ h : BHist,
      locatedIntervalSupremumDecodeBHist
          (locatedIntervalSupremumEncodeBHist h) =
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

def locatedIntervalSupremumToEventFlow :
    LocatedIntervalSupremumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalSupremumUp.mk intervalSource upperBound lowerApprox bisection
      window readback realSeal transport replay provenance name =>
      [[BMark.b0],
        locatedIntervalSupremumEncodeBHist intervalSource,
        [BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist upperBound,
        [BMark.b1, BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist lowerApprox,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist bisection,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        locatedIntervalSupremumEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        locatedIntervalSupremumEncodeBHist name]

def locatedIntervalSupremumFromEventFlow :
    EventFlow → Option LocatedIntervalSupremumUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | intervalSource :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | upperBound :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | lowerApprox :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | bisection :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | window :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | readback :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | realSeal :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | replay :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (LocatedIntervalSupremumUp.mk
                                                                                                  (locatedIntervalSupremumDecodeBHist intervalSource)
                                                                                                  (locatedIntervalSupremumDecodeBHist upperBound)
                                                                                                  (locatedIntervalSupremumDecodeBHist lowerApprox)
                                                                                                  (locatedIntervalSupremumDecodeBHist bisection)
                                                                                                  (locatedIntervalSupremumDecodeBHist window)
                                                                                                  (locatedIntervalSupremumDecodeBHist readback)
                                                                                                  (locatedIntervalSupremumDecodeBHist realSeal)
                                                                                                  (locatedIntervalSupremumDecodeBHist transport)
                                                                                                  (locatedIntervalSupremumDecodeBHist replay)
                                                                                                  (locatedIntervalSupremumDecodeBHist provenance)
                                                                                                  (locatedIntervalSupremumDecodeBHist name))
                                                                                          | _ :: _ => none

private theorem locatedIntervalSupremum_round_trip :
    ∀ x : LocatedIntervalSupremumUp,
      locatedIntervalSupremumFromEventFlow
          (locatedIntervalSupremumToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk intervalSource upperBound lowerApprox bisection window readback realSeal
      transport replay provenance name =>
      change
        some
          (LocatedIntervalSupremumUp.mk
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist intervalSource))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist upperBound))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist lowerApprox))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist bisection))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist window))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist readback))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist realSeal))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist transport))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist replay))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist provenance))
            (locatedIntervalSupremumDecodeBHist
              (locatedIntervalSupremumEncodeBHist name))) =
          some
            (LocatedIntervalSupremumUp.mk intervalSource upperBound lowerApprox
              bisection window readback realSeal transport replay provenance name)
      rw [locatedIntervalSupremumDecode_encode_bhist intervalSource,
        locatedIntervalSupremumDecode_encode_bhist upperBound,
        locatedIntervalSupremumDecode_encode_bhist lowerApprox,
        locatedIntervalSupremumDecode_encode_bhist bisection,
        locatedIntervalSupremumDecode_encode_bhist window,
        locatedIntervalSupremumDecode_encode_bhist readback,
        locatedIntervalSupremumDecode_encode_bhist realSeal,
        locatedIntervalSupremumDecode_encode_bhist transport,
        locatedIntervalSupremumDecode_encode_bhist replay,
        locatedIntervalSupremumDecode_encode_bhist provenance,
        locatedIntervalSupremumDecode_encode_bhist name]

private theorem locatedIntervalSupremumToEventFlow_injective
    {x y : LocatedIntervalSupremumUp} :
    locatedIntervalSupremumToEventFlow x =
        locatedIntervalSupremumToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalSupremumFromEventFlow
          (locatedIntervalSupremumToEventFlow x) =
        locatedIntervalSupremumFromEventFlow
          (locatedIntervalSupremumToEventFlow y) :=
    congrArg locatedIntervalSupremumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedIntervalSupremum_round_trip x).symm
      (Eq.trans hread (locatedIntervalSupremum_round_trip y)))

instance locatedIntervalSupremumBHistCarrier :
    BHistCarrier LocatedIntervalSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalSupremumToEventFlow
  fromEventFlow := locatedIntervalSupremumFromEventFlow

instance locatedIntervalSupremumChapterTasteGate :
    ChapterTasteGate LocatedIntervalSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedIntervalSupremumFromEventFlow
          (locatedIntervalSupremumToEventFlow x) =
        some x
    exact locatedIntervalSupremum_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalSupremumToEventFlow_injective heq)

theorem LocatedIntervalSupremumTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedIntervalSupremumDecodeBHist
          (locatedIntervalSupremumEncodeBHist h) =
        h) ∧
      (∀ x : LocatedIntervalSupremumUp,
        locatedIntervalSupremumFromEventFlow
            (locatedIntervalSupremumToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedIntervalSupremumUp,
          locatedIntervalSupremumToEventFlow x =
              locatedIntervalSupremumToEventFlow y →
            x = y) ∧
          locatedIntervalSupremumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact locatedIntervalSupremumDecode_encode_bhist
  · constructor
    · exact locatedIntervalSupremum_round_trip
    · constructor
      · intro x y heq
        exact locatedIntervalSupremumToEventFlow_injective heq
      · rfl

end BEDC.Derived.LocatedIntervalSupremumUp
