import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RademacherUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RademacherUp : Type where
  | mk (lipschitz real dyadic metric absolute transport replay provenance name :
      BHist) : RademacherUp
  deriving DecidableEq

def rademacherEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rademacherEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rademacherEncodeBHist h

def rademacherDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rademacherDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rademacherDecodeBHist tail)

private theorem rademacherDecode_encode_bhist :
    ∀ h : BHist, rademacherDecodeBHist (rademacherEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def rademacherToEventFlow : RademacherUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RademacherUp.mk lipschitz real dyadic metric absolute transport replay provenance name =>
      [[BMark.b0],
        rademacherEncodeBHist lipschitz,
        [BMark.b1, BMark.b0],
        rademacherEncodeBHist real,
        [BMark.b1, BMark.b1, BMark.b0],
        rademacherEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rademacherEncodeBHist metric,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rademacherEncodeBHist absolute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rademacherEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        rademacherEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        rademacherEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        rademacherEncodeBHist name]

def rademacherFields : RademacherUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RademacherUp.mk lipschitz real dyadic metric absolute transport replay provenance name =>
      [lipschitz, real, dyadic, metric, absolute, transport, replay, provenance, name]

def rademacherFromEventFlow : EventFlow → Option RademacherUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | lipschitz :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | real :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | dyadic :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | metric :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | absolute :: rest9 =>
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
                                                                                (RademacherUp.mk
                                                                                  (rademacherDecodeBHist
                                                                                    lipschitz)
                                                                                  (rademacherDecodeBHist
                                                                                    real)
                                                                                  (rademacherDecodeBHist
                                                                                    dyadic)
                                                                                  (rademacherDecodeBHist
                                                                                    metric)
                                                                                  (rademacherDecodeBHist
                                                                                    absolute)
                                                                                  (rademacherDecodeBHist
                                                                                    transport)
                                                                                  (rademacherDecodeBHist
                                                                                    replay)
                                                                                  (rademacherDecodeBHist
                                                                                    provenance)
                                                                                  (rademacherDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem rademacher_round_trip :
    ∀ x : RademacherUp,
      rademacherFromEventFlow (rademacherToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lipschitz real dyadic metric absolute transport replay provenance name =>
      change
        some
          (RademacherUp.mk
            (rademacherDecodeBHist (rademacherEncodeBHist lipschitz))
            (rademacherDecodeBHist (rademacherEncodeBHist real))
            (rademacherDecodeBHist (rademacherEncodeBHist dyadic))
            (rademacherDecodeBHist (rademacherEncodeBHist metric))
            (rademacherDecodeBHist (rademacherEncodeBHist absolute))
            (rademacherDecodeBHist (rademacherEncodeBHist transport))
            (rademacherDecodeBHist (rademacherEncodeBHist replay))
            (rademacherDecodeBHist (rademacherEncodeBHist provenance))
            (rademacherDecodeBHist (rademacherEncodeBHist name))) =
          some
            (RademacherUp.mk lipschitz real dyadic metric absolute transport replay
              provenance name)
      rw [rademacherDecode_encode_bhist lipschitz, rademacherDecode_encode_bhist real,
        rademacherDecode_encode_bhist dyadic, rademacherDecode_encode_bhist metric,
        rademacherDecode_encode_bhist absolute, rademacherDecode_encode_bhist transport,
        rademacherDecode_encode_bhist replay, rademacherDecode_encode_bhist provenance,
        rademacherDecode_encode_bhist name]

private theorem rademacherToEventFlow_injective {x y : RademacherUp} :
    rademacherToEventFlow x = rademacherToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rademacherFromEventFlow (rademacherToEventFlow x) =
        rademacherFromEventFlow (rademacherToEventFlow y) :=
    congrArg rademacherFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rademacher_round_trip x).symm
      (Eq.trans hread (rademacher_round_trip y)))

private theorem rademacherFields_faithful :
    ∀ x y : RademacherUp, rademacherFields x = rademacherFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk lipschitz real dyadic metric absolute transport replay provenance name =>
      cases y with
      | mk lipschitz' real' dyadic' metric' absolute' transport' replay' provenance' name' =>
          cases hfields
          rfl

instance rademacherBHistCarrier : BHistCarrier RademacherUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rademacherToEventFlow
  fromEventFlow := rademacherFromEventFlow

instance rademacherChapterTasteGate : ChapterTasteGate RademacherUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rademacherFromEventFlow (rademacherToEventFlow x) = some x
    exact rademacher_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rademacherToEventFlow_injective heq)

instance rademacherFieldFaithful : FieldFaithful RademacherUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rademacherFields
  field_faithful := rademacherFields_faithful

instance rademacherNontrivial : Nontrivial RademacherUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RademacherUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RademacherUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

namespace TasteGate

theorem RademacherTasteGate_single_carrier_alignment :
    (∀ h : BHist, rademacherDecodeBHist (rademacherEncodeBHist h) = h) ∧
      (∀ x : RademacherUp, rademacherFromEventFlow (rademacherToEventFlow x) = some x) ∧
        (∀ x y : RademacherUp,
          rademacherToEventFlow x = rademacherToEventFlow y → x = y) ∧
          rademacherEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RademacherUp, rademacherFields x = rademacherFields y → x = y) ∧
              (∃ x y : RademacherUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact rademacherDecode_encode_bhist
  · constructor
    · exact rademacher_round_trip
    · constructor
      · intro x y heq
        exact rademacherToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact rademacherFields_faithful
          · exact
              ⟨RademacherUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                RademacherUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end TasteGate

end BEDC.Derived.RademacherUp
