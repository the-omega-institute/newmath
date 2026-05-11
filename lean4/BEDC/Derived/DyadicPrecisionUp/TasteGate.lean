import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# DyadicPrecisionUp TasteGate carrier.
-/

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite precision schedule token with the seven BEDC rows visible to consumers. -/
inductive DyadicPrecisionUp : Type where
  | mk :
      (precision radius window transport provenance nameCert ledger : BHist) →
      DyadicPrecisionUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def dyadicPrecisionToEventFlow : DyadicPrecisionUp → EventFlow
  | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
      [[BMark.b0],
        encodeBHist precision,
        [BMark.b1, BMark.b0],
        encodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist nameCert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist ledger]

private def dyadicPrecisionFromEventFlow : EventFlow → Option DyadicPrecisionUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | precision :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | radius :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | window :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | transport :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | provenance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | nameCert :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | ledger :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (DyadicPrecisionUp.mk
                                                                  (decodeBHist precision)
                                                                  (decodeBHist radius)
                                                                  (decodeBHist window)
                                                                  (decodeBHist transport)
                                                                  (decodeBHist provenance)
                                                                  (decodeBHist nameCert)
                                                                  (decodeBHist ledger))
                                                          | _ :: _ => none

private theorem dyadicPrecision_round_trip :
    ∀ x : DyadicPrecisionUp,
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x := by
  intro x
  cases x with
  | mk precision radius window transport provenance nameCert ledger =>
      change
        some
          (DyadicPrecisionUp.mk
            (decodeBHist (encodeBHist precision)) (decodeBHist (encodeBHist radius))
            (decodeBHist (encodeBHist window)) (decodeBHist (encodeBHist transport))
            (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist nameCert))
            (decodeBHist (encodeBHist ledger))) =
          some
            (DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger)
      rw [decode_encode_bhist precision, decode_encode_bhist radius,
        decode_encode_bhist window, decode_encode_bhist transport,
        decode_encode_bhist provenance, decode_encode_bhist nameCert, decode_encode_bhist ledger]

private theorem dyadicPrecisionToEventFlow_injective {x y : DyadicPrecisionUp} :
    dyadicPrecisionToEventFlow x = dyadicPrecisionToEventFlow y → x = y := by
  intro heq
  have hread :
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) =
        dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow y) :=
    congrArg dyadicPrecisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicPrecision_round_trip x).symm
      (Eq.trans hread (dyadicPrecision_round_trip y)))

instance dyadicPrecisionBHistCarrier : BHistCarrier DyadicPrecisionUp where
  toEventFlow := dyadicPrecisionToEventFlow
  fromEventFlow := dyadicPrecisionFromEventFlow

instance dyadicPrecisionChapterTasteGate : ChapterTasteGate DyadicPrecisionUp where
  round_trip := by
    intro x
    change dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x
    exact dyadicPrecision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicPrecisionToEventFlow_injective heq)

theorem DyadicPrecisionScheduleTasteGate_visible_rows :
    (∀ x : DyadicPrecisionUp,
      dyadicPrecisionFromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (∀ x y : DyadicPrecisionUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) ∧
        (∀ (x : DyadicPrecisionUp) w m, List.Mem w (BHistCarrier.toEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x
    exact dyadicPrecision_round_trip x
  · constructor
    · intro x y heq
      exact dyadicPrecisionToEventFlow_injective heq
    · intro x w m hw hm
      exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm

/-- Public gate object for the finite dyadic-precision schedule carrier. -/
def taste_gate : ChapterTasteGate DyadicPrecisionUp :=
  dyadicPrecisionChapterTasteGate

end BEDC.Derived.DyadicPrecisionUp
