import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetacicConfluenceAuditWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetacicConfluenceAuditWitnessUp : Type where
  | mk (parallel substitution diamond confluence obstruction component route ledger name :
      BHist) : MetacicConfluenceAuditWitnessUp
  deriving DecidableEq

def metacicConfluenceAuditWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicConfluenceAuditWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicConfluenceAuditWitnessEncodeBHist h

def metacicConfluenceAuditWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicConfluenceAuditWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicConfluenceAuditWitnessDecodeBHist tail)

private theorem metacicConfluenceAuditWitnessDecode_encode_bhist :
    ∀ h : BHist,
      metacicConfluenceAuditWitnessDecodeBHist
        (metacicConfluenceAuditWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metacicConfluenceAuditWitnessToEventFlow :
    MetacicConfluenceAuditWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetacicConfluenceAuditWitnessUp.mk parallel substitution diamond confluence obstruction
      component route ledger name =>
      [[BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist parallel,
        [BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist substitution,
        [BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist diamond,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist confluence,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist component,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metacicConfluenceAuditWitnessEncodeBHist name]

def metacicConfluenceAuditWitnessFromEventFlow :
    EventFlow → Option MetacicConfluenceAuditWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | parallel :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | substitution :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | diamond :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | confluence :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | obstruction :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | component :: rest11 =>
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
                                                              | ledger :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetacicConfluenceAuditWitnessUp.mk
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    parallel)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    substitution)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    diamond)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    confluence)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    obstruction)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    component)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    route)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    ledger)
                                                                                  (metacicConfluenceAuditWitnessDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem metacicConfluenceAuditWitness_round_trip :
    ∀ x : MetacicConfluenceAuditWitnessUp,
      metacicConfluenceAuditWitnessFromEventFlow
        (metacicConfluenceAuditWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk parallel substitution diamond confluence obstruction component route ledger name =>
      change
        some
          (MetacicConfluenceAuditWitnessUp.mk
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist parallel))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist substitution))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist diamond))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist confluence))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist obstruction))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist component))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist route))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist ledger))
            (metacicConfluenceAuditWitnessDecodeBHist
              (metacicConfluenceAuditWitnessEncodeBHist name))) =
          some
            (MetacicConfluenceAuditWitnessUp.mk parallel substitution diamond confluence
              obstruction component route ledger name)
      rw [metacicConfluenceAuditWitnessDecode_encode_bhist parallel,
        metacicConfluenceAuditWitnessDecode_encode_bhist substitution,
        metacicConfluenceAuditWitnessDecode_encode_bhist diamond,
        metacicConfluenceAuditWitnessDecode_encode_bhist confluence,
        metacicConfluenceAuditWitnessDecode_encode_bhist obstruction,
        metacicConfluenceAuditWitnessDecode_encode_bhist component,
        metacicConfluenceAuditWitnessDecode_encode_bhist route,
        metacicConfluenceAuditWitnessDecode_encode_bhist ledger,
        metacicConfluenceAuditWitnessDecode_encode_bhist name]

private theorem metacicConfluenceAuditWitnessToEventFlow_injective
    {x y : MetacicConfluenceAuditWitnessUp} :
    metacicConfluenceAuditWitnessToEventFlow x =
        metacicConfluenceAuditWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow x) =
        metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow y) :=
    congrArg metacicConfluenceAuditWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicConfluenceAuditWitness_round_trip x).symm
      (Eq.trans hread (metacicConfluenceAuditWitness_round_trip y)))

instance metacicConfluenceAuditWitnessBHistCarrier :
    BHistCarrier MetacicConfluenceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicConfluenceAuditWitnessToEventFlow
  fromEventFlow := metacicConfluenceAuditWitnessFromEventFlow

instance metacicConfluenceAuditWitnessFieldFaithful :
    FieldFaithful MetacicConfluenceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetacicConfluenceAuditWitnessUp.mk parallel substitution diamond confluence
        obstruction component route ledger name =>
        [parallel, substitution, diamond, confluence, obstruction, component, route,
          ledger, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk parallel substitution diamond confluence obstruction component route ledger name =>
        cases y with
        | mk parallel' substitution' diamond' confluence' obstruction' component' route'
            ledger' name' =>
            cases hfields
            rfl

instance metacicConfluenceAuditWitnessChapterTasteGate :
    ChapterTasteGate MetacicConfluenceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicConfluenceAuditWitnessFromEventFlow
        (metacicConfluenceAuditWitnessToEventFlow x) = some x
    exact metacicConfluenceAuditWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicConfluenceAuditWitnessToEventFlow_injective heq)

instance metacicConfluenceAuditWitnessNontrivial :
    Nontrivial MetacicConfluenceAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetacicConfluenceAuditWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetacicConfluenceAuditWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem MetacicConfluenceAuditWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metacicConfluenceAuditWitnessDecodeBHist
          (metacicConfluenceAuditWitnessEncodeBHist h) = h) ∧
      (∀ x : MetacicConfluenceAuditWitnessUp,
        metacicConfluenceAuditWitnessFromEventFlow
          (metacicConfluenceAuditWitnessToEventFlow x) = some x) ∧
        (∀ x y : MetacicConfluenceAuditWitnessUp,
          metacicConfluenceAuditWitnessToEventFlow x =
              metacicConfluenceAuditWitnessToEventFlow y →
            x = y) ∧
          metacicConfluenceAuditWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metacicConfluenceAuditWitnessDecode_encode_bhist
  · constructor
    · exact metacicConfluenceAuditWitness_round_trip
    · constructor
      · intro x y heq
        exact metacicConfluenceAuditWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetacicConfluenceAuditWitnessUp
