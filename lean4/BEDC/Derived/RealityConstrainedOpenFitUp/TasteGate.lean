import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedOpenFitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedOpenFitUp : Type where
  | mk :
      (trace bundle observed model fit continuation ledger refutation nameRow : BHist) →
      RealityConstrainedOpenFitUp
  deriving DecidableEq

def realityConstrainedOpenFitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedOpenFitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedOpenFitEncodeBHist h

def realityConstrainedOpenFitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedOpenFitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedOpenFitDecodeBHist tail)

private theorem realityConstrainedOpenFitDecode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedOpenFitDecodeBHist (realityConstrainedOpenFitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedOpenFitToEventFlow : RealityConstrainedOpenFitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation ledger
      refutation nameRow =>
      [[BMark.b0],
        realityConstrainedOpenFitEncodeBHist trace,
        [BMark.b1, BMark.b0],
        realityConstrainedOpenFitEncodeBHist bundle,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedOpenFitEncodeBHist observed,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedOpenFitEncodeBHist model,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedOpenFitEncodeBHist fit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedOpenFitEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedOpenFitEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedOpenFitEncodeBHist refutation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedOpenFitEncodeBHist nameRow]

def realityConstrainedOpenFitFromEventFlow : EventFlow → Option RealityConstrainedOpenFitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | trace :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | bundle :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | observed :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | model :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | fit :: rest9 =>
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
                                                      | ledger :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | refutation :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameRow :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RealityConstrainedOpenFitUp.mk
                                                                                  (realityConstrainedOpenFitDecodeBHist trace)
                                                                                  (realityConstrainedOpenFitDecodeBHist bundle)
                                                                                  (realityConstrainedOpenFitDecodeBHist observed)
                                                                                  (realityConstrainedOpenFitDecodeBHist model)
                                                                                  (realityConstrainedOpenFitDecodeBHist fit)
                                                                                  (realityConstrainedOpenFitDecodeBHist continuation)
                                                                                  (realityConstrainedOpenFitDecodeBHist ledger)
                                                                                  (realityConstrainedOpenFitDecodeBHist refutation)
                                                                                  (realityConstrainedOpenFitDecodeBHist nameRow))
                                                                          | _ :: _ => none

private theorem realityConstrainedOpenFit_round_trip :
    ∀ x : RealityConstrainedOpenFitUp,
      realityConstrainedOpenFitFromEventFlow (realityConstrainedOpenFitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk trace bundle observed model fit continuation ledger refutation nameRow =>
      change
        some (RealityConstrainedOpenFitUp.mk
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist trace))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist bundle))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist observed))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist model))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist fit))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist continuation))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist ledger))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist refutation))
          (realityConstrainedOpenFitDecodeBHist
            (realityConstrainedOpenFitEncodeBHist nameRow))) =
          some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation
            ledger refutation nameRow)
      have hTrace :
          some (RealityConstrainedOpenFitUp.mk
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist trace))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist bundle))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist observed))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist model))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist fit))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist continuation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist ledger))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist bundle))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist observed))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist model))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist bundle))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist observed))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist model))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist trace)
      have hBundle :
          some (RealityConstrainedOpenFitUp.mk trace
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist bundle))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist observed))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist model))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist fit))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist continuation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist ledger))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist observed))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist model))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist observed))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist model))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist bundle)
      have hObserved :
          some (RealityConstrainedOpenFitUp.mk trace bundle
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist observed))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist model))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist fit))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist continuation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist ledger))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle observed
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist model))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace bundle row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist model))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist observed)
      have hModel :
          some (RealityConstrainedOpenFitUp.mk trace bundle observed
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist model))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist fit))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist continuation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist ledger))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace bundle observed row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist fit))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist model)
      have hFit :
          some (RealityConstrainedOpenFitUp.mk trace bundle observed model
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist fit))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist continuation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist ledger))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist continuation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist fit)
      have hContinuation :
          some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist continuation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist ledger))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit
              continuation
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist ledger))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist continuation)
      have hLedger :
          some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist ledger))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit
              continuation ledger
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation
              row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist refutation))
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist ledger)
      have hRefutation :
          some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation
            ledger
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist refutation))
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit
              continuation ledger refutation
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation
              ledger row
              (realityConstrainedOpenFitDecodeBHist
                (realityConstrainedOpenFitEncodeBHist nameRow))))
          (realityConstrainedOpenFitDecode_encode_bhist refutation)
      have hNameRow :
          some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation
            ledger refutation
            (realityConstrainedOpenFitDecodeBHist
              (realityConstrainedOpenFitEncodeBHist nameRow))) =
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit
              continuation ledger refutation nameRow) :=
        congrArg
          (fun row =>
            some (RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation
              ledger refutation row))
          (realityConstrainedOpenFitDecode_encode_bhist nameRow)
      exact
        hTrace.trans
          (hBundle.trans
            (hObserved.trans
              (hModel.trans
                (hFit.trans
                  (hContinuation.trans (hLedger.trans (hRefutation.trans hNameRow)))))))

instance realityConstrainedOpenFitBHistCarrier :
    BHistCarrier RealityConstrainedOpenFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedOpenFitToEventFlow
  fromEventFlow := realityConstrainedOpenFitFromEventFlow

instance realityConstrainedOpenFitChapterTasteGate :
    ChapterTasteGate RealityConstrainedOpenFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := realityConstrainedOpenFit_round_trip
  layer_separation := by
    intro x y hxy flowEq
    apply hxy
    have optionEq :
        realityConstrainedOpenFitFromEventFlow (realityConstrainedOpenFitToEventFlow x) =
          realityConstrainedOpenFitFromEventFlow (realityConstrainedOpenFitToEventFlow y) := by
      exact congrArg realityConstrainedOpenFitFromEventFlow flowEq
    rw [realityConstrainedOpenFit_round_trip x] at optionEq
    rw [realityConstrainedOpenFit_round_trip y] at optionEq
    exact Option.some.inj optionEq

instance realityConstrainedOpenFitFieldFaithful :
    FieldFaithful RealityConstrainedOpenFitUp where
  fields := fun x =>
    match x with
    | RealityConstrainedOpenFitUp.mk trace bundle observed model fit continuation ledger
        refutation nameRow =>
        [trace, bundle, observed, model, fit, continuation, ledger, refutation, nameRow]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk trace₁ bundle₁ observed₁ model₁ fit₁ continuation₁ ledger₁ refutation₁ nameRow₁ =>
        cases y with
        | mk trace₂ bundle₂ observed₂ model₂ fit₂ continuation₂ ledger₂ refutation₂ nameRow₂ =>
            simp only at h
            injection h with hTrace t1
            injection t1 with hBundle t2
            injection t2 with hObserved t3
            injection t3 with hModel t4
            injection t4 with hFit t5
            injection t5 with hContinuation t6
            injection t6 with hLedger t7
            injection t7 with hRefutation t8
            injection t8 with hNameRow _
            subst hTrace
            subst hBundle
            subst hObserved
            subst hModel
            subst hFit
            subst hContinuation
            subst hLedger
            subst hRefutation
            subst hNameRow
            rfl

instance realityConstrainedOpenFitNontrivial :
    Nontrivial RealityConstrainedOpenFitUp where
  witness_pair :=
    ⟨RealityConstrainedOpenFitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedOpenFitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealityConstrainedOpenFitTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealityConstrainedOpenFitUp) ∧
      Nonempty (FieldFaithful RealityConstrainedOpenFitUp) ∧
        (∀ x : RealityConstrainedOpenFitUp,
          ∃ w : RawEvent, List.Mem w (BHistCarrier.toEventFlow x) ∧
            (List.Mem BMark.b0 w ∨ List.Mem BMark.b1 w)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro inferInstance
  · constructor
    · exact Nonempty.intro inferInstance
    · intro x
      cases x with
      | mk trace bundle observed model fit continuation ledger refutation nameRow =>
          exact
            ⟨[BMark.b0],
              (List.Mem.head _),
              Or.inl (List.Mem.head _)⟩

end BEDC.Derived.RealityConstrainedOpenFitUp.TasteGate
