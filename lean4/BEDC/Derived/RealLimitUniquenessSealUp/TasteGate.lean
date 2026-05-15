import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLimitUniquenessSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLimitUniquenessSealUp : Type where
  | mk :
      (firstSeal secondSeal comparison finiteWindow dyadicLedger realClassifier uniqueness
        transport continuation provenance name : BHist) →
      RealLimitUniquenessSealUp
  deriving DecidableEq

def realLimitUniquenessSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLimitUniquenessSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLimitUniquenessSealEncodeBHist h

def realLimitUniquenessSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLimitUniquenessSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLimitUniquenessSealDecodeBHist tail)

private theorem realLimitUniquenessSeal_decode_encode_bhist :
    ∀ h : BHist,
      realLimitUniquenessSealDecodeBHist
        (realLimitUniquenessSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realLimitUniquenessSealFields : RealLimitUniquenessSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLimitUniquenessSealUp.mk firstSeal secondSeal comparison finiteWindow dyadicLedger
      realClassifier uniqueness transport continuation provenance name =>
      [firstSeal, secondSeal, comparison, finiteWindow, dyadicLedger, realClassifier,
        uniqueness, transport, continuation, provenance, name]

def realLimitUniquenessSealToEventFlow : RealLimitUniquenessSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealLimitUniquenessSealUp.mk firstSeal secondSeal comparison finiteWindow dyadicLedger
      realClassifier uniqueness transport continuation provenance name =>
      [[BMark.b0],
        realLimitUniquenessSealEncodeBHist firstSeal,
        [BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist secondSeal,
        [BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist comparison,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist finiteWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist realClassifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist uniqueness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realLimitUniquenessSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessSealEncodeBHist name]

def realLimitUniquenessSealFromEventFlow : EventFlow → Option RealLimitUniquenessSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | firstSeal :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | secondSeal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | comparison :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | finiteWindow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadicLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realClassifier :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | uniqueness :: rest13 =>
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
                                                                      | continuation :: rest17 =>
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
                                                                                                (RealLimitUniquenessSealUp.mk
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    firstSeal)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    secondSeal)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    comparison)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    finiteWindow)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    dyadicLedger)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    realClassifier)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    uniqueness)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    transport)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    continuation)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    provenance)
                                                                                                  (realLimitUniquenessSealDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ => none

private theorem realLimitUniquenessSeal_round_trip :
    ∀ x : RealLimitUniquenessSealUp,
      realLimitUniquenessSealFromEventFlow
        (realLimitUniquenessSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk firstSeal secondSeal comparison finiteWindow dyadicLedger realClassifier uniqueness
      transport continuation provenance name =>
      change
        some
          (RealLimitUniquenessSealUp.mk
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist firstSeal))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist secondSeal))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist comparison))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist finiteWindow))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist dyadicLedger))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist realClassifier))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist uniqueness))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist transport))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist continuation))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist provenance))
            (realLimitUniquenessSealDecodeBHist
              (realLimitUniquenessSealEncodeBHist name))) =
          some
            (RealLimitUniquenessSealUp.mk firstSeal secondSeal comparison finiteWindow
              dyadicLedger realClassifier uniqueness transport continuation provenance name)
      rw [realLimitUniquenessSeal_decode_encode_bhist firstSeal,
        realLimitUniquenessSeal_decode_encode_bhist secondSeal,
        realLimitUniquenessSeal_decode_encode_bhist comparison,
        realLimitUniquenessSeal_decode_encode_bhist finiteWindow,
        realLimitUniquenessSeal_decode_encode_bhist dyadicLedger,
        realLimitUniquenessSeal_decode_encode_bhist realClassifier,
        realLimitUniquenessSeal_decode_encode_bhist uniqueness,
        realLimitUniquenessSeal_decode_encode_bhist transport,
        realLimitUniquenessSeal_decode_encode_bhist continuation,
        realLimitUniquenessSeal_decode_encode_bhist provenance,
        realLimitUniquenessSeal_decode_encode_bhist name]

private theorem realLimitUniquenessSealToEventFlow_injective
    {x y : RealLimitUniquenessSealUp} :
    realLimitUniquenessSealToEventFlow x = realLimitUniquenessSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLimitUniquenessSealFromEventFlow (realLimitUniquenessSealToEventFlow x) =
        realLimitUniquenessSealFromEventFlow (realLimitUniquenessSealToEventFlow y) :=
    congrArg realLimitUniquenessSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realLimitUniquenessSeal_round_trip x).symm
      (Eq.trans hread (realLimitUniquenessSeal_round_trip y)))

private theorem realLimitUniquenessSeal_field_faithful :
    ∀ x y : RealLimitUniquenessSealUp,
      realLimitUniquenessSealFields x = realLimitUniquenessSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk firstSeal secondSeal comparison finiteWindow dyadicLedger realClassifier uniqueness
      transport continuation provenance name =>
      cases y with
      | mk firstSeal' secondSeal' comparison' finiteWindow' dyadicLedger' realClassifier'
          uniqueness' transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance realLimitUniquenessSealBHistCarrier :
    BHistCarrier RealLimitUniquenessSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLimitUniquenessSealToEventFlow
  fromEventFlow := realLimitUniquenessSealFromEventFlow

instance realLimitUniquenessSealChapterTasteGate :
    ChapterTasteGate RealLimitUniquenessSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLimitUniquenessSealFromEventFlow (realLimitUniquenessSealToEventFlow x) =
      some x
    exact realLimitUniquenessSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLimitUniquenessSealToEventFlow_injective heq)

instance realLimitUniquenessSealFieldFaithful :
    FieldFaithful RealLimitUniquenessSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realLimitUniquenessSealFields
  field_faithful := realLimitUniquenessSeal_field_faithful

instance realLimitUniquenessSealNontrivial : Nontrivial RealLimitUniquenessSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealLimitUniquenessSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealLimitUniquenessSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealLimitUniquenessSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realLimitUniquenessSealChapterTasteGate

theorem RealLimitUniquenessSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realLimitUniquenessSealDecodeBHist (realLimitUniquenessSealEncodeBHist h) = h) ∧
      (∀ x : RealLimitUniquenessSealUp,
        realLimitUniquenessSealFromEventFlow (realLimitUniquenessSealToEventFlow x) =
          some x) ∧
        (∀ x y : RealLimitUniquenessSealUp,
          realLimitUniquenessSealToEventFlow x = realLimitUniquenessSealToEventFlow y →
            x = y) ∧
          realLimitUniquenessSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realLimitUniquenessSeal_decode_encode_bhist
  · constructor
    · exact realLimitUniquenessSeal_round_trip
    · constructor
      · intro x y heq
        exact realLimitUniquenessSealToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealLimitUniquenessSealUp
