import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicPrecisionUp : Type where
  | mk :
      (n rho window hsameRows contRows provenance cert ledger : BHist) → DyadicPrecisionUp
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
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def dyadicPrecisionToEventFlow : DyadicPrecisionUp → EventFlow
  | DyadicPrecisionUp.mk n rho window hsameRows contRows provenance cert ledger =>
      [[BMark.b0], encodeBHist n,
        [BMark.b1, BMark.b0], encodeBHist rho,
        [BMark.b1, BMark.b1, BMark.b0], encodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist hsameRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist contRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist cert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          encodeBHist ledger]

private def dyadicPrecisionFromEventFlow : EventFlow → Option DyadicPrecisionUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | n :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rho :: rest3 =>
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
                              | hsameRows :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | contRows :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | cert :: rest13 =>
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
                                                                          (decodeBHist n)
                                                                          (decodeBHist rho)
                                                                          (decodeBHist window)
                                                                          (decodeBHist hsameRows)
                                                                          (decodeBHist contRows)
                                                                          (decodeBHist provenance)
                                                                          (decodeBHist cert)
                                                                          (decodeBHist ledger))
                                                                  | _ :: _ => none

private theorem dyadicPrecision_round_trip :
    ∀ x : DyadicPrecisionUp,
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x := by
  intro x
  cases x with
  | mk n rho window hsameRows contRows provenance cert ledger =>
      change
        some
            (DyadicPrecisionUp.mk (decodeBHist (encodeBHist n))
              (decodeBHist (encodeBHist rho)) (decodeBHist (encodeBHist window))
              (decodeBHist (encodeBHist hsameRows)) (decodeBHist (encodeBHist contRows))
              (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
              (decodeBHist (encodeBHist ledger))) =
          some (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance cert ledger)
      have hN :
          some
              (DyadicPrecisionUp.mk (decodeBHist (encodeBHist n))
                (decodeBHist (encodeBHist rho)) (decodeBHist (encodeBHist window))
                (decodeBHist (encodeBHist hsameRows)) (decodeBHist (encodeBHist contRows))
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))) =
            some
              (DyadicPrecisionUp.mk n (decodeBHist (encodeBHist rho))
                (decodeBHist (encodeBHist window)) (decodeBHist (encodeBHist hsameRows))
                (decodeBHist (encodeBHist contRows)) (decodeBHist (encodeBHist provenance))
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some
              (DyadicPrecisionUp.mk row (decodeBHist (encodeBHist rho))
                (decodeBHist (encodeBHist window)) (decodeBHist (encodeBHist hsameRows))
                (decodeBHist (encodeBHist contRows)) (decodeBHist (encodeBHist provenance))
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist n)
      have hRho :
          some
              (DyadicPrecisionUp.mk n (decodeBHist (encodeBHist rho))
                (decodeBHist (encodeBHist window)) (decodeBHist (encodeBHist hsameRows))
                (decodeBHist (encodeBHist contRows)) (decodeBHist (encodeBHist provenance))
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) =
            some
              (DyadicPrecisionUp.mk n rho (decodeBHist (encodeBHist window))
                (decodeBHist (encodeBHist hsameRows)) (decodeBHist (encodeBHist contRows))
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some
              (DyadicPrecisionUp.mk n row (decodeBHist (encodeBHist window))
                (decodeBHist (encodeBHist hsameRows)) (decodeBHist (encodeBHist contRows))
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist rho)
      have hWindow :
          some
              (DyadicPrecisionUp.mk n rho (decodeBHist (encodeBHist window))
                (decodeBHist (encodeBHist hsameRows)) (decodeBHist (encodeBHist contRows))
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))) =
            some
              (DyadicPrecisionUp.mk n rho window (decodeBHist (encodeBHist hsameRows))
                (decodeBHist (encodeBHist contRows)) (decodeBHist (encodeBHist provenance))
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some
              (DyadicPrecisionUp.mk n rho row (decodeBHist (encodeBHist hsameRows))
                (decodeBHist (encodeBHist contRows)) (decodeBHist (encodeBHist provenance))
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist window)
      have hSameRows :
          some
              (DyadicPrecisionUp.mk n rho window (decodeBHist (encodeBHist hsameRows))
                (decodeBHist (encodeBHist contRows)) (decodeBHist (encodeBHist provenance))
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) =
            some
              (DyadicPrecisionUp.mk n rho window hsameRows (decodeBHist (encodeBHist contRows))
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some
              (DyadicPrecisionUp.mk n rho window row (decodeBHist (encodeBHist contRows))
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist hsameRows)
      have hContRows :
          some
              (DyadicPrecisionUp.mk n rho window hsameRows (decodeBHist (encodeBHist contRows))
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))) =
            some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some
              (DyadicPrecisionUp.mk n rho window hsameRows row
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist contRows)
      have hProvenance :
          some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows
                (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist cert))
                (decodeBHist (encodeBHist ledger))) =
            some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows row
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist provenance)
      have hCert :
          some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance
                (decodeBHist (encodeBHist cert)) (decodeBHist (encodeBHist ledger))) =
            some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance cert
                (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance row
                (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist cert)
      have hLedger :
          some
              (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance cert
                (decodeBHist (encodeBHist ledger))) =
            some (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance cert ledger) :=
        congrArg
          (fun row => some (DyadicPrecisionUp.mk n rho window hsameRows contRows provenance cert row))
          (decode_encode_bhist ledger)
      exact Eq.trans hN
        (Eq.trans hRho
          (Eq.trans hWindow
            (Eq.trans hSameRows
              (Eq.trans hContRows (Eq.trans hProvenance (Eq.trans hCert hLedger))))))

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

theorem DyadicPrecisionScheduleCarrier_single_carrier_alignment :
    ChapterTasteGate DyadicPrecisionUp ∧
      (forall x : DyadicPrecisionUp,
        exists n rho window hsameRows contRows provenance cert ledger : BHist,
          x = DyadicPrecisionUp.mk n rho window hsameRows contRows provenance cert ledger) := by
  constructor
  · exact dyadicPrecisionChapterTasteGate
  · intro x
    cases x with
    | mk n rho window hsameRows contRows provenance cert ledger =>
        exact ⟨n, rho, window, hsameRows, contRows, provenance, cert, ledger, rfl⟩

end BEDC.Derived.DyadicPrecisionUp
