import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TasteGateStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TasteGateStabilityUp : Type where
  | mk :
      (candidate carrier tasteGate witness admission transport replay provenance name : BHist) →
      TasteGateStabilityUp
  deriving DecidableEq

def tasteGateStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tasteGateStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tasteGateStabilityEncodeBHist h

def tasteGateStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tasteGateStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tasteGateStabilityDecodeBHist tail)

private theorem tasteGateStabilityDecode_encode_bhist :
    ∀ h : BHist, tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tasteGateStabilityToEventFlow : TasteGateStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TasteGateStabilityUp.mk candidate carrier tasteGate witness admission transport replay
      provenance name =>
      [[BMark.b0],
        tasteGateStabilityEncodeBHist candidate,
        [BMark.b1, BMark.b0],
        tasteGateStabilityEncodeBHist carrier,
        [BMark.b1, BMark.b1, BMark.b0],
        tasteGateStabilityEncodeBHist tasteGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateStabilityEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateStabilityEncodeBHist admission,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateStabilityEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tasteGateStabilityEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tasteGateStabilityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tasteGateStabilityEncodeBHist name]

def tasteGateStabilityFromEventFlow : EventFlow → Option TasteGateStabilityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | candidate :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | carrier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | tasteGate :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | witness :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | admission :: rest9 =>
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
                                                                                (TasteGateStabilityUp.mk
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    candidate)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    carrier)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    tasteGate)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    witness)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    admission)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    transport)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    replay)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    provenance)
                                                                                  (tasteGateStabilityDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem tasteGateStability_round_trip :
    ∀ x : TasteGateStabilityUp,
      tasteGateStabilityFromEventFlow (tasteGateStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk candidate carrier tasteGate witness admission transport replay provenance name =>
      change
        some
          (TasteGateStabilityUp.mk
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist candidate))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist carrier))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist tasteGate))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist witness))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist admission))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist transport))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist replay))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist provenance))
            (tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist name))) =
          some
            (TasteGateStabilityUp.mk candidate carrier tasteGate witness admission transport
              replay provenance name)
      rw [tasteGateStabilityDecode_encode_bhist candidate,
        tasteGateStabilityDecode_encode_bhist carrier,
        tasteGateStabilityDecode_encode_bhist tasteGate,
        tasteGateStabilityDecode_encode_bhist witness,
        tasteGateStabilityDecode_encode_bhist admission,
        tasteGateStabilityDecode_encode_bhist transport,
        tasteGateStabilityDecode_encode_bhist replay,
        tasteGateStabilityDecode_encode_bhist provenance,
        tasteGateStabilityDecode_encode_bhist name]

private theorem tasteGateStabilityToEventFlow_injective {x y : TasteGateStabilityUp} :
    tasteGateStabilityToEventFlow x = tasteGateStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tasteGateStabilityFromEventFlow (tasteGateStabilityToEventFlow x) =
        tasteGateStabilityFromEventFlow (tasteGateStabilityToEventFlow y) :=
    congrArg tasteGateStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (tasteGateStability_round_trip x).symm
      (Eq.trans hread (tasteGateStability_round_trip y)))

instance tasteGateStabilityBHistCarrier : BHistCarrier TasteGateStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tasteGateStabilityToEventFlow
  fromEventFlow := tasteGateStabilityFromEventFlow

instance tasteGateStabilityChapterTasteGate : ChapterTasteGate TasteGateStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tasteGateStabilityFromEventFlow (tasteGateStabilityToEventFlow x) = some x
    exact tasteGateStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tasteGateStabilityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TasteGateStabilityUp :=
  tasteGateStabilityChapterTasteGate

theorem TasteGateStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist, tasteGateStabilityDecodeBHist (tasteGateStabilityEncodeBHist h) = h) ∧
      (∀ x : TasteGateStabilityUp,
        tasteGateStabilityFromEventFlow (tasteGateStabilityToEventFlow x) = some x) ∧
        (∀ x y : TasteGateStabilityUp,
          tasteGateStabilityToEventFlow x = tasteGateStabilityToEventFlow y → x = y) ∧
          tasteGateStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact tasteGateStabilityDecode_encode_bhist
  · constructor
    · exact tasteGateStability_round_trip
    · constructor
      · intro x y heq
        exact tasteGateStabilityToEventFlow_injective heq
      · rfl

end BEDC.Derived.TasteGateStabilityUp
