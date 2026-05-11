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

/-- Finite precision schedule token with the eight BEDC rows visible to consumers. -/
inductive DyadicPrecisionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (precision radius window hrow crow pkgRow nameRow ledger : BHist) →
      DyadicPrecisionUp

private def encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def dyadicPrecisionToEventFlow : DyadicPrecisionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicPrecisionUp.mk precision radius window hrow crow pkgRow nameRow ledger =>
      [[BMark.b0],
        encodeBHist precision,
        [BMark.b1, BMark.b0],
        encodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist hrow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist crow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist pkgRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist nameRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        encodeBHist ledger]

private def dyadicPrecisionFromEventFlow : EventFlow → Option DyadicPrecisionUp
  -- BEDC touchpoint anchor: BHist BMark
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
                              | hrow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | crow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | pkgRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nameRow :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | ledger :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DyadicPrecisionUp.mk
                                                                          (decodeBHist precision)
                                                                          (decodeBHist radius)
                                                                          (decodeBHist window)
                                                                          (decodeBHist hrow)
                                                                          (decodeBHist crow)
                                                                          (decodeBHist pkgRow)
                                                                          (decodeBHist nameRow)
                                                                          (decodeBHist ledger))
                                                                  | _ :: _ => none

private theorem dyadicPrecision_round_trip :
    ∀ x : DyadicPrecisionUp,
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision radius window hrow crow pkgRow nameRow ledger =>
      change
        some (DyadicPrecisionUp.mk (decodeBHist (encodeBHist precision))
          (decodeBHist (encodeBHist radius)) (decodeBHist (encodeBHist window))
          (decodeBHist (encodeBHist hrow)) (decodeBHist (encodeBHist crow))
          (decodeBHist (encodeBHist pkgRow)) (decodeBHist (encodeBHist nameRow))
          (decodeBHist (encodeBHist ledger))) =
          some
            (DyadicPrecisionUp.mk precision radius window hrow crow pkgRow nameRow ledger)
      rw [decode_encode_bhist precision, decode_encode_bhist radius,
        decode_encode_bhist window, decode_encode_bhist hrow, decode_encode_bhist crow,
        decode_encode_bhist pkgRow, decode_encode_bhist nameRow, decode_encode_bhist ledger]

private theorem dyadicPrecisionToEventFlow_injective {x y : DyadicPrecisionUp} :
    dyadicPrecisionToEventFlow x = dyadicPrecisionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) =
        dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow y) :=
    congrArg dyadicPrecisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicPrecision_round_trip x).symm
      (Eq.trans hread (dyadicPrecision_round_trip y)))

instance dyadicPrecisionBHistCarrier : BHistCarrier DyadicPrecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicPrecisionToEventFlow
  fromEventFlow := dyadicPrecisionFromEventFlow

instance dyadicPrecisionChapterTasteGate : ChapterTasteGate DyadicPrecisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x
    exact dyadicPrecision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicPrecisionToEventFlow_injective heq)

/-- Public gate object for the finite dyadic-precision schedule carrier. -/
def taste_gate : ChapterTasteGate DyadicPrecisionUp :=
  dyadicPrecisionChapterTasteGate

theorem DyadicPrecisionSchedule_empty_branch_readback
    {rho window hrow crow pkgRow nameRow ledger : BHist} :
    BHistCarrier.fromEventFlow
        (BHistCarrier.toEventFlow
          (DyadicPrecisionUp.mk BHist.Empty rho window hrow crow pkgRow nameRow ledger)) =
      some (DyadicPrecisionUp.mk BHist.Empty rho window hrow crow pkgRow nameRow ledger) := by
  -- BEDC touchpoint anchor: BHist BMark
  change
    dyadicPrecisionFromEventFlow
        (dyadicPrecisionToEventFlow
          (DyadicPrecisionUp.mk BHist.Empty rho window hrow crow pkgRow nameRow ledger)) =
      some (DyadicPrecisionUp.mk BHist.Empty rho window hrow crow pkgRow nameRow ledger)
  exact dyadicPrecision_round_trip
    (DyadicPrecisionUp.mk BHist.Empty rho window hrow crow pkgRow nameRow ledger)

end BEDC.Derived.DyadicPrecisionUp
