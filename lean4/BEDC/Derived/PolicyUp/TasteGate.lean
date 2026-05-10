import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolicyUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolicyUp : Type where
  | mk : (belief markov randomvar estimator decision ledger : BHist) → PolicyUp
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

private def policyToEventFlow : PolicyUp → EventFlow
  | PolicyUp.mk belief markov randomvar estimator decision ledger =>
      [[BMark.b0], encodeBHist belief,
        [BMark.b1, BMark.b0], encodeBHist markov,
        [BMark.b1, BMark.b1, BMark.b0], encodeBHist randomvar,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist estimator,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist ledger]

private def policyFromEventFlow : EventFlow → Option PolicyUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | belief :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | markov :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | randomvar :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | estimator :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | decision :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (PolicyUp.mk (decodeBHist belief)
                                                          (decodeBHist markov)
                                                          (decodeBHist randomvar)
                                                          (decodeBHist estimator)
                                                          (decodeBHist decision)
                                                          (decodeBHist ledger))
                                                  | _ :: _ => none

private theorem policy_round_trip :
    ∀ x : PolicyUp, policyFromEventFlow (policyToEventFlow x) = some x := by
  intro x
  cases x with
  | mk belief markov randomvar estimator decision ledger =>
      change
        some (PolicyUp.mk (decodeBHist (encodeBHist belief))
          (decodeBHist (encodeBHist markov)) (decodeBHist (encodeBHist randomvar))
          (decodeBHist (encodeBHist estimator)) (decodeBHist (encodeBHist decision))
          (decodeBHist (encodeBHist ledger))) =
          some (PolicyUp.mk belief markov randomvar estimator decision ledger)
      have hBelief :
          some (PolicyUp.mk (decodeBHist (encodeBHist belief))
            (decodeBHist (encodeBHist markov)) (decodeBHist (encodeBHist randomvar))
            (decodeBHist (encodeBHist estimator)) (decodeBHist (encodeBHist decision))
            (decodeBHist (encodeBHist ledger))) =
            some (PolicyUp.mk belief (decodeBHist (encodeBHist markov))
              (decodeBHist (encodeBHist randomvar)) (decodeBHist (encodeBHist estimator))
              (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (PolicyUp.mk row (decodeBHist (encodeBHist markov))
              (decodeBHist (encodeBHist randomvar)) (decodeBHist (encodeBHist estimator))
              (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist belief)
      have hMarkov :
          some (PolicyUp.mk belief (decodeBHist (encodeBHist markov))
            (decodeBHist (encodeBHist randomvar)) (decodeBHist (encodeBHist estimator))
            (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))) =
            some (PolicyUp.mk belief markov (decodeBHist (encodeBHist randomvar))
              (decodeBHist (encodeBHist estimator)) (decodeBHist (encodeBHist decision))
              (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (PolicyUp.mk belief row (decodeBHist (encodeBHist randomvar))
              (decodeBHist (encodeBHist estimator)) (decodeBHist (encodeBHist decision))
              (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist markov)
      have hRandomvar :
          some (PolicyUp.mk belief markov (decodeBHist (encodeBHist randomvar))
            (decodeBHist (encodeBHist estimator)) (decodeBHist (encodeBHist decision))
            (decodeBHist (encodeBHist ledger))) =
            some (PolicyUp.mk belief markov randomvar (decodeBHist (encodeBHist estimator))
              (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (PolicyUp.mk belief markov row (decodeBHist (encodeBHist estimator))
              (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist randomvar)
      have hEstimator :
          some (PolicyUp.mk belief markov randomvar (decodeBHist (encodeBHist estimator))
            (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))) =
            some (PolicyUp.mk belief markov randomvar estimator
              (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (PolicyUp.mk belief markov randomvar row
              (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist estimator)
      have hDecision :
          some (PolicyUp.mk belief markov randomvar estimator
            (decodeBHist (encodeBHist decision)) (decodeBHist (encodeBHist ledger))) =
            some (PolicyUp.mk belief markov randomvar estimator decision
              (decodeBHist (encodeBHist ledger))) :=
        congrArg
          (fun row =>
            some (PolicyUp.mk belief markov randomvar estimator row
              (decodeBHist (encodeBHist ledger))))
          (decode_encode_bhist decision)
      have hLedger :
          some (PolicyUp.mk belief markov randomvar estimator decision
            (decodeBHist (encodeBHist ledger))) =
            some (PolicyUp.mk belief markov randomvar estimator decision ledger) :=
        congrArg
          (fun row => some (PolicyUp.mk belief markov randomvar estimator decision row))
          (decode_encode_bhist ledger)
      exact Eq.trans hBelief
        (Eq.trans hMarkov
          (Eq.trans hRandomvar (Eq.trans hEstimator (Eq.trans hDecision hLedger))))

private theorem policyToEventFlow_injective {x y : PolicyUp} :
    policyToEventFlow x = policyToEventFlow y → x = y := by
  intro heq
  have hread : policyFromEventFlow (policyToEventFlow x) = policyFromEventFlow (policyToEventFlow y) :=
    congrArg policyFromEventFlow heq
  exact Option.some.inj (Eq.trans (policy_round_trip x).symm (Eq.trans hread (policy_round_trip y)))

instance policyBHistCarrier : BHistCarrier PolicyUp where
  toEventFlow := policyToEventFlow
  fromEventFlow := policyFromEventFlow

instance policyChapterTasteGate : ChapterTasteGate PolicyUp where
  round_trip := by
    intro x
    change policyFromEventFlow (policyToEventFlow x) = some x
    exact policy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (policyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PolicyUp where
  round_trip := by
    intro x
    change policyFromEventFlow (policyToEventFlow x) = some x
    exact policy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (policyToEventFlow_injective heq)

end BEDC.Derived.PolicyUp
