import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolicyUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolicyUp : Type where
  | mk : (belief markov randomVar estimator : BHist) → PolicyUp
  deriving DecidableEq

def PolicyEventFlow_left_inverse_encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: PolicyEventFlow_left_inverse_encodeBHist h
  | BHist.e1 h => BMark.b1 :: PolicyEventFlow_left_inverse_encodeBHist h

def PolicyEventFlow_left_inverse_decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (PolicyEventFlow_left_inverse_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (PolicyEventFlow_left_inverse_decodeBHist tail)

theorem PolicyEventFlow_left_inverse_decode_encode_bhist :
    ∀ h : BHist,
      PolicyEventFlow_left_inverse_decodeBHist
        (PolicyEventFlow_left_inverse_encodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def policyToEventFlow : PolicyUp → EventFlow
  | PolicyUp.mk belief markov randomVar estimator =>
      [[BMark.b0], PolicyEventFlow_left_inverse_encodeBHist belief,
        [BMark.b1, BMark.b0], PolicyEventFlow_left_inverse_encodeBHist markov,
        [BMark.b1, BMark.b1, BMark.b0],
          PolicyEventFlow_left_inverse_encodeBHist randomVar,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          PolicyEventFlow_left_inverse_encodeBHist estimator]

def policyFromEventFlow : EventFlow → Option PolicyUp
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
                      | randomVar :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | estimator :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (PolicyUp.mk
                                          (PolicyEventFlow_left_inverse_decodeBHist belief)
                                          (PolicyEventFlow_left_inverse_decodeBHist markov)
                                          (PolicyEventFlow_left_inverse_decodeBHist randomVar)
                                          (PolicyEventFlow_left_inverse_decodeBHist estimator))
                                  | _ :: _ => none

theorem PolicyEventFlow_left_inverse
    (belief markov randomVar estimator : BHist) :
    policyFromEventFlow (policyToEventFlow (PolicyUp.mk belief markov randomVar estimator)) =
      some (PolicyUp.mk belief markov randomVar estimator) := by
  change
    some
        (PolicyUp.mk
          (PolicyEventFlow_left_inverse_decodeBHist
            (PolicyEventFlow_left_inverse_encodeBHist belief))
          (PolicyEventFlow_left_inverse_decodeBHist
            (PolicyEventFlow_left_inverse_encodeBHist markov))
          (PolicyEventFlow_left_inverse_decodeBHist
            (PolicyEventFlow_left_inverse_encodeBHist randomVar))
          (PolicyEventFlow_left_inverse_decodeBHist
            (PolicyEventFlow_left_inverse_encodeBHist estimator))) =
      some (PolicyUp.mk belief markov randomVar estimator)
  have hBelief :
      some
          (PolicyUp.mk
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist belief))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist markov))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist randomVar))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))) =
        some
          (PolicyUp.mk belief
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist markov))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist randomVar))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))) :=
    congrArg
      (fun row =>
        some
          (PolicyUp.mk row
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist markov))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist randomVar))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))))
      (PolicyEventFlow_left_inverse_decode_encode_bhist belief)
  have hMarkov :
      some
          (PolicyUp.mk belief
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist markov))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist randomVar))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))) =
        some
          (PolicyUp.mk belief markov
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist randomVar))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))) :=
    congrArg
      (fun row =>
        some
          (PolicyUp.mk belief row
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist randomVar))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))))
      (PolicyEventFlow_left_inverse_decode_encode_bhist markov)
  have hRandomVar :
      some
          (PolicyUp.mk belief markov
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist randomVar))
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))) =
        some
          (PolicyUp.mk belief markov randomVar
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))) :=
    congrArg
      (fun row =>
        some
          (PolicyUp.mk belief markov row
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))))
      (PolicyEventFlow_left_inverse_decode_encode_bhist randomVar)
  have hEstimator :
      some
          (PolicyUp.mk belief markov randomVar
            (PolicyEventFlow_left_inverse_decodeBHist
              (PolicyEventFlow_left_inverse_encodeBHist estimator))) =
        some (PolicyUp.mk belief markov randomVar estimator) :=
    congrArg
      (fun row => some (PolicyUp.mk belief markov randomVar row))
      (PolicyEventFlow_left_inverse_decode_encode_bhist estimator)
  exact Eq.trans hBelief (Eq.trans hMarkov (Eq.trans hRandomVar hEstimator))

instance policyBHistCarrier : BHistCarrier PolicyUp where
  toEventFlow := policyToEventFlow
  fromEventFlow := policyFromEventFlow

instance policyChapterTasteGate : ChapterTasteGate PolicyUp where
  round_trip := by
    intro x
    cases x with
    | mk belief markov randomVar estimator =>
        exact PolicyEventFlow_left_inverse belief markov randomVar estimator
  layer_separation := by
    intro x y hxy heq
    apply hxy
    have hread :
        policyFromEventFlow (policyToEventFlow x) =
          policyFromEventFlow (policyToEventFlow y) :=
      congrArg policyFromEventFlow heq
    cases x with
    | mk beliefX markovX randomVarX estimatorX =>
    cases y with
    | mk beliefY markovY randomVarY estimatorY =>
    exact Option.some.inj
      (Eq.trans
        (PolicyEventFlow_left_inverse beliefX markovX randomVarX estimatorX).symm
        (Eq.trans hread
          (PolicyEventFlow_left_inverse beliefY markovY randomVarY estimatorY)))

def taste_gate : ChapterTasteGate PolicyUp :=
  policyChapterTasteGate

end BEDC.Derived.PolicyUp
