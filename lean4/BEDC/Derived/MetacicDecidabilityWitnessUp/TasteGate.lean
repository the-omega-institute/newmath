import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacicDecidabilityWitnessUp : Type where
  | mk (typing sameTerm bounded finished refusal transport route provenance name :
      BHist) : MetacicDecidabilityWitnessUp
  deriving DecidableEq

def metacicDecidabilityWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicDecidabilityWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicDecidabilityWitnessEncodeBHist h

def metacicDecidabilityWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicDecidabilityWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicDecidabilityWitnessDecodeBHist tail)

private theorem metacicDecidabilityWitnessDecode_encode_bhist :
    ∀ h : BHist,
      metacicDecidabilityWitnessDecodeBHist
        (metacicDecidabilityWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicDecidabilityWitnessToEventFlow :
    MetacicDecidabilityWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicDecidabilityWitnessUp.mk typing sameTerm bounded finished refusal transport
      route provenance name =>
      [[BMark.b0],
        metacicDecidabilityWitnessEncodeBHist typing,
        [BMark.b1, BMark.b0],
        metacicDecidabilityWitnessEncodeBHist sameTerm,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicDecidabilityWitnessEncodeBHist bounded,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidabilityWitnessEncodeBHist finished,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidabilityWitnessEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidabilityWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicDecidabilityWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicDecidabilityWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicDecidabilityWitnessEncodeBHist name]

def metacicDecidabilityWitnessFromEventFlow :
    EventFlow → Option MetacicDecidabilityWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | typing :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sameTerm :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | bounded :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | finished :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
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
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetacicDecidabilityWitnessUp.mk
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    typing)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    sameTerm)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    bounded)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    finished)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    refusal)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    transport)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    route)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    provenance)
                                                                                  (metacicDecidabilityWitnessDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem metacicDecidabilityWitness_round_trip :
    ∀ x : MetacicDecidabilityWitnessUp,
      metacicDecidabilityWitnessFromEventFlow
        (metacicDecidabilityWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typing sameTerm bounded finished refusal transport route provenance name =>
      change
        some
          (MetacicDecidabilityWitnessUp.mk
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist typing))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist sameTerm))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist bounded))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist finished))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist refusal))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist transport))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist route))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist provenance))
            (metacicDecidabilityWitnessDecodeBHist
              (metacicDecidabilityWitnessEncodeBHist name))) =
          some
            (MetacicDecidabilityWitnessUp.mk typing sameTerm bounded finished refusal
              transport route provenance name)
      rw [metacicDecidabilityWitnessDecode_encode_bhist typing,
        metacicDecidabilityWitnessDecode_encode_bhist sameTerm,
        metacicDecidabilityWitnessDecode_encode_bhist bounded,
        metacicDecidabilityWitnessDecode_encode_bhist finished,
        metacicDecidabilityWitnessDecode_encode_bhist refusal,
        metacicDecidabilityWitnessDecode_encode_bhist transport,
        metacicDecidabilityWitnessDecode_encode_bhist route,
        metacicDecidabilityWitnessDecode_encode_bhist provenance,
        metacicDecidabilityWitnessDecode_encode_bhist name]

private theorem metacicDecidabilityWitnessToEventFlow_injective
    {x y : MetacicDecidabilityWitnessUp} :
    metacicDecidabilityWitnessToEventFlow x =
        metacicDecidabilityWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicDecidabilityWitnessFromEventFlow
          (metacicDecidabilityWitnessToEventFlow x) =
        metacicDecidabilityWitnessFromEventFlow
          (metacicDecidabilityWitnessToEventFlow y) :=
    congrArg metacicDecidabilityWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicDecidabilityWitness_round_trip x).symm
      (Eq.trans hread (metacicDecidabilityWitness_round_trip y)))

instance metacicDecidabilityWitnessBHistCarrier :
    BHistCarrier MetacicDecidabilityWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicDecidabilityWitnessToEventFlow
  fromEventFlow := metacicDecidabilityWitnessFromEventFlow

instance metacicDecidabilityWitnessChapterTasteGate :
    ChapterTasteGate MetacicDecidabilityWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicDecidabilityWitnessFromEventFlow
        (metacicDecidabilityWitnessToEventFlow x) = some x
    exact metacicDecidabilityWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicDecidabilityWitnessToEventFlow_injective heq)

theorem MetacicDecidabilityWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metacicDecidabilityWitnessDecodeBHist
          (metacicDecidabilityWitnessEncodeBHist h) = h) ∧
      (∀ x : MetacicDecidabilityWitnessUp,
        metacicDecidabilityWitnessFromEventFlow
          (metacicDecidabilityWitnessToEventFlow x) = some x) ∧
        (∀ x y : MetacicDecidabilityWitnessUp,
          metacicDecidabilityWitnessToEventFlow x =
              metacicDecidabilityWitnessToEventFlow y →
            x = y) ∧
          metacicDecidabilityWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicDecidabilityWitnessDecode_encode_bhist
  · constructor
    · exact metacicDecidabilityWitness_round_trip
    · constructor
      · intro x y heq
        exact metacicDecidabilityWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetacicDecidabilityWitnessUp
