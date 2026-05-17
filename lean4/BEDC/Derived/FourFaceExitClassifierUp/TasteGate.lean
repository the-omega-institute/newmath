import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FourFaceExitClassifierUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FourFaceExitClassifierUp : Type where
  | mk :
      (stream tolerance readback realSeal transport continuation provenance name : BHist) →
      FourFaceExitClassifierUp
  deriving DecidableEq

def fourFaceExitClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fourFaceExitClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fourFaceExitClassifierEncodeBHist h

def fourFaceExitClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fourFaceExitClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fourFaceExitClassifierDecodeBHist tail)

private theorem fourFaceExitClassifier_decode_encode_bhist :
    ∀ h : BHist,
      fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fourFaceExitClassifierFields : FourFaceExitClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FourFaceExitClassifierUp.mk stream tolerance readback realSeal transport continuation
      provenance name =>
      [stream, tolerance, readback, realSeal, transport, continuation, provenance, name]

def fourFaceExitClassifierToEventFlow : FourFaceExitClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FourFaceExitClassifierUp.mk stream tolerance readback realSeal transport continuation
      provenance name =>
      [[BMark.b0],
        fourFaceExitClassifierEncodeBHist stream,
        [BMark.b1, BMark.b0],
        fourFaceExitClassifierEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b0],
        fourFaceExitClassifierEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fourFaceExitClassifierEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fourFaceExitClassifierEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fourFaceExitClassifierEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        fourFaceExitClassifierEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        fourFaceExitClassifierEncodeBHist name]

def fourFaceExitClassifierFromEventFlow :
    EventFlow → Option FourFaceExitClassifierUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | stream :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | tolerance :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (FourFaceExitClassifierUp.mk
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            stream)
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            tolerance)
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            readback)
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            realSeal)
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            transport)
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            continuation)
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            provenance)
                                                                          (fourFaceExitClassifierDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem fourFaceExitClassifier_round_trip :
    ∀ x : FourFaceExitClassifierUp,
      fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream tolerance readback realSeal transport continuation provenance name =>
      change
        some
          (FourFaceExitClassifierUp.mk
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist stream))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist tolerance))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist readback))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist realSeal))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist transport))
            (fourFaceExitClassifierDecodeBHist
              (fourFaceExitClassifierEncodeBHist continuation))
            (fourFaceExitClassifierDecodeBHist
              (fourFaceExitClassifierEncodeBHist provenance))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist name))) =
          some
            (FourFaceExitClassifierUp.mk stream tolerance readback realSeal transport
              continuation provenance name)
      rw [fourFaceExitClassifier_decode_encode_bhist stream,
        fourFaceExitClassifier_decode_encode_bhist tolerance,
        fourFaceExitClassifier_decode_encode_bhist readback,
        fourFaceExitClassifier_decode_encode_bhist realSeal,
        fourFaceExitClassifier_decode_encode_bhist transport,
        fourFaceExitClassifier_decode_encode_bhist continuation,
        fourFaceExitClassifier_decode_encode_bhist provenance,
        fourFaceExitClassifier_decode_encode_bhist name]

private theorem fourFaceExitClassifierToEventFlow_injective
    {x y : FourFaceExitClassifierUp} :
    fourFaceExitClassifierToEventFlow x = fourFaceExitClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) =
        fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow y) :=
    congrArg fourFaceExitClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fourFaceExitClassifier_round_trip x).symm
      (Eq.trans hread (fourFaceExitClassifier_round_trip y)))

private theorem fourFaceExitClassifier_field_faithful :
    ∀ x y : FourFaceExitClassifierUp,
      fourFaceExitClassifierFields x = fourFaceExitClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk stream tolerance readback realSeal transport continuation provenance name =>
      cases y with
      | mk stream' tolerance' readback' realSeal' transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance fourFaceExitClassifierBHistCarrier : BHistCarrier FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fourFaceExitClassifierToEventFlow
  fromEventFlow := fourFaceExitClassifierFromEventFlow

instance fourFaceExitClassifierChapterTasteGate :
    ChapterTasteGate FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) = some x
    exact fourFaceExitClassifier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fourFaceExitClassifierToEventFlow_injective heq)

instance fourFaceExitClassifierFieldFaithful : FieldFaithful FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fourFaceExitClassifierFields
  field_faithful := fourFaceExitClassifier_field_faithful

instance fourFaceExitClassifierNontrivial : Nontrivial FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FourFaceExitClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FourFaceExitClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FourFaceExitClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem FourFaceExitClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist h) = h) ∧
      (∀ x : FourFaceExitClassifierUp,
        fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) =
          some x) ∧
        (∀ x y : FourFaceExitClassifierUp,
          fourFaceExitClassifierToEventFlow x = fourFaceExitClassifierToEventFlow y →
            x = y) ∧
          fourFaceExitClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact fourFaceExitClassifier_decode_encode_bhist
  · constructor
    · exact fourFaceExitClassifier_round_trip
    · constructor
      · intro x y heq
        exact fourFaceExitClassifierToEventFlow_injective heq
      · rfl

namespace TasteGate

theorem FourFaceExitClassifierNameCertObligations
    (stream tolerance readback realSeal transport continuation provenance name : BHist) :
    fourFaceExitClassifierFields
        (FourFaceExitClassifierUp.mk stream tolerance readback realSeal transport continuation
          provenance name) =
      [stream, tolerance, readback, realSeal, transport, continuation, provenance, name] ∧
      Cont stream tolerance (append stream tolerance) ∧
        Cont readback realSeal (append readback realSeal) ∧
          hsame (append readback realSeal) (append readback realSeal) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · exact hsame_refl (append readback realSeal)

end TasteGate

end BEDC.Derived.FourFaceExitClassifierUp
