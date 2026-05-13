import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionSealClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionSealClassifierUp : Type where
  | mk :
      (agreementSeal limitSeal synchronizer budget regularHandoff streamWindow dyadicLedger
        transport route provenance name : BHist) →
      RealCompletionSealClassifierUp
  deriving DecidableEq

def realCompletionSealClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionSealClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionSealClassifierEncodeBHist h

def realCompletionSealClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionSealClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionSealClassifierDecodeBHist tail)

private theorem realCompletionSealClassifier_decode_encode_bhist :
    ∀ h : BHist,
      realCompletionSealClassifierDecodeBHist
        (realCompletionSealClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realCompletionSealClassifierFields :
    RealCompletionSealClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionSealClassifierUp.mk agreementSeal limitSeal synchronizer budget
      regularHandoff streamWindow dyadicLedger transport route provenance name =>
      [agreementSeal, limitSeal, synchronizer, budget, regularHandoff, streamWindow,
        dyadicLedger, transport, route, provenance, name]

def realCompletionSealClassifierToEventFlow :
    RealCompletionSealClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionSealClassifierUp.mk agreementSeal limitSeal synchronizer budget
      regularHandoff streamWindow dyadicLedger transport route provenance name =>
      [[BMark.b0],
        realCompletionSealClassifierEncodeBHist agreementSeal,
        [BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist synchronizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist regularHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist streamWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realCompletionSealClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realCompletionSealClassifierEncodeBHist name]

def realCompletionSealClassifierFromEventFlow :
    EventFlow → Option RealCompletionSealClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | agreementSeal :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | limitSeal :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | synchronizer :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | budget :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | regularHandoff :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | streamWindow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | dyadicLedger :: rest13 =>
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
                                                                      | route :: rest17 =>
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
                                                                                                (RealCompletionSealClassifierUp.mk
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    agreementSeal)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    limitSeal)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    synchronizer)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    budget)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    regularHandoff)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    streamWindow)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    dyadicLedger)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    transport)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    route)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    provenance)
                                                                                                  (realCompletionSealClassifierDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ => none

private theorem realCompletionSealClassifier_round_trip :
    ∀ x : RealCompletionSealClassifierUp,
      realCompletionSealClassifierFromEventFlow
        (realCompletionSealClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk agreementSeal limitSeal synchronizer budget regularHandoff streamWindow
      dyadicLedger transport route provenance name =>
      change
        some
          (RealCompletionSealClassifierUp.mk
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist agreementSeal))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist limitSeal))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist synchronizer))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist budget))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist regularHandoff))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist streamWindow))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist dyadicLedger))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist transport))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist route))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist provenance))
            (realCompletionSealClassifierDecodeBHist
              (realCompletionSealClassifierEncodeBHist name))) =
          some
            (RealCompletionSealClassifierUp.mk agreementSeal limitSeal synchronizer budget
              regularHandoff streamWindow dyadicLedger transport route provenance name)
      rw [realCompletionSealClassifier_decode_encode_bhist agreementSeal,
        realCompletionSealClassifier_decode_encode_bhist limitSeal,
        realCompletionSealClassifier_decode_encode_bhist synchronizer,
        realCompletionSealClassifier_decode_encode_bhist budget,
        realCompletionSealClassifier_decode_encode_bhist regularHandoff,
        realCompletionSealClassifier_decode_encode_bhist streamWindow,
        realCompletionSealClassifier_decode_encode_bhist dyadicLedger,
        realCompletionSealClassifier_decode_encode_bhist transport,
        realCompletionSealClassifier_decode_encode_bhist route,
        realCompletionSealClassifier_decode_encode_bhist provenance,
        realCompletionSealClassifier_decode_encode_bhist name]

private theorem realCompletionSealClassifierToEventFlow_injective
    {x y : RealCompletionSealClassifierUp} :
    realCompletionSealClassifierToEventFlow x =
      realCompletionSealClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionSealClassifierFromEventFlow
          (realCompletionSealClassifierToEventFlow x) =
        realCompletionSealClassifierFromEventFlow
          (realCompletionSealClassifierToEventFlow y) :=
    congrArg realCompletionSealClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionSealClassifier_round_trip x).symm
      (Eq.trans hread (realCompletionSealClassifier_round_trip y)))

private theorem RealCompletionSealClassifierTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RealCompletionSealClassifierUp,
      realCompletionSealClassifierFields x = realCompletionSealClassifierFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk agreementSeal limitSeal synchronizer budget regularHandoff streamWindow dyadicLedger
      transport route provenance name =>
      cases y with
      | mk agreementSeal' limitSeal' synchronizer' budget' regularHandoff' streamWindow'
          dyadicLedger' transport' route' provenance' name' =>
          cases hfields
          rfl

instance realCompletionSealClassifierBHistCarrier :
    BHistCarrier RealCompletionSealClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionSealClassifierToEventFlow
  fromEventFlow := realCompletionSealClassifierFromEventFlow

instance realCompletionSealClassifierChapterTasteGate :
    ChapterTasteGate RealCompletionSealClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionSealClassifierFromEventFlow
        (realCompletionSealClassifierToEventFlow x) = some x
    exact realCompletionSealClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionSealClassifierToEventFlow_injective heq)

instance realCompletionSealClassifierFieldFaithful :
    FieldFaithful RealCompletionSealClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realCompletionSealClassifierFields
  field_faithful :=
    RealCompletionSealClassifierTasteGate_single_carrier_alignment_field_faithful

instance realCompletionSealClassifierNontrivial :
    Nontrivial RealCompletionSealClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealCompletionSealClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealCompletionSealClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealCompletionSealClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletionSealClassifierChapterTasteGate

theorem RealCompletionSealClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realCompletionSealClassifierDecodeBHist
        (realCompletionSealClassifierEncodeBHist h) = h) ∧
      (∀ x : RealCompletionSealClassifierUp,
        realCompletionSealClassifierFromEventFlow
          (realCompletionSealClassifierToEventFlow x) = some x) ∧
        (∀ x y : RealCompletionSealClassifierUp,
          realCompletionSealClassifierToEventFlow x =
            realCompletionSealClassifierToEventFlow y → x = y) ∧
          realCompletionSealClassifierEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RealCompletionSealClassifierUp,
              realCompletionSealClassifierFields x =
                realCompletionSealClassifierFields y → x = y) ∧
              (∃ x y : RealCompletionSealClassifierUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realCompletionSealClassifier_decode_encode_bhist
  · constructor
    · exact realCompletionSealClassifier_round_trip
    · constructor
      · intro x y heq
        exact realCompletionSealClassifierToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact RealCompletionSealClassifierTasteGate_single_carrier_alignment_field_faithful
          · exact
              ⟨RealCompletionSealClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                RealCompletionSealClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.RealCompletionSealClassifierUp
