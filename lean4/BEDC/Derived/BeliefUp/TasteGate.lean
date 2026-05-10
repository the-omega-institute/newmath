import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

/-!
# BeliefUp: single-carrier packet and TasteGate instance.
-/

namespace BEDC.Derived.BeliefUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- A finite belief packet carrying the five chapter rows. -/
inductive BeliefUp : Type where
  | mk : (prior observation updateTrace probability evidence : BHist) → BeliefUp
  deriving DecidableEq

/-- Marker-level coding of a `BHist` row. -/
def encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

/-- Readback for the marker-level coding of a `BHist` row. -/
def decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

/-- Display embedding of the five chapter rows into the ground event flow. -/
def beliefToEventFlow : BeliefUp → EventFlow
  | BeliefUp.mk prior observation updateTrace probability evidence =>
      [[BMark.b0], encodeBHist prior,
        [BMark.b1, BMark.b0], encodeBHist observation,
        [BMark.b1, BMark.b1, BMark.b0], encodeBHist updateTrace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist probability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist evidence]

def beliefFromEventFlow : EventFlow → Option BeliefUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | prior :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observation :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | updateTrace :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | probability :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | evidence :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some (BeliefUp.mk (decodeBHist prior)
                                                (decodeBHist observation) (decodeBHist updateTrace)
                                                (decodeBHist probability) (decodeBHist evidence))
                                          | _ :: _ => none

theorem belief_round_trip :
    ∀ x : BeliefUp, beliefFromEventFlow (beliefToEventFlow x) = some x := by
  intro x
  cases x with
  | mk prior observation updateTrace probability evidence =>
      change
        some (BeliefUp.mk (decodeBHist (encodeBHist prior))
          (decodeBHist (encodeBHist observation)) (decodeBHist (encodeBHist updateTrace))
          (decodeBHist (encodeBHist probability)) (decodeBHist (encodeBHist evidence))) =
          some (BeliefUp.mk prior observation updateTrace probability evidence)
      have hPrior :
          some (BeliefUp.mk (decodeBHist (encodeBHist prior))
            (decodeBHist (encodeBHist observation)) (decodeBHist (encodeBHist updateTrace))
            (decodeBHist (encodeBHist probability)) (decodeBHist (encodeBHist evidence))) =
            some (BeliefUp.mk prior (decodeBHist (encodeBHist observation))
              (decodeBHist (encodeBHist updateTrace)) (decodeBHist (encodeBHist probability))
              (decodeBHist (encodeBHist evidence))) :=
        congrArg
          (fun row =>
            some (BeliefUp.mk row (decodeBHist (encodeBHist observation))
              (decodeBHist (encodeBHist updateTrace)) (decodeBHist (encodeBHist probability))
              (decodeBHist (encodeBHist evidence))))
          (decode_encode_bhist prior)
      have hObservation :
          some (BeliefUp.mk prior (decodeBHist (encodeBHist observation))
            (decodeBHist (encodeBHist updateTrace)) (decodeBHist (encodeBHist probability))
            (decodeBHist (encodeBHist evidence))) =
            some (BeliefUp.mk prior observation (decodeBHist (encodeBHist updateTrace))
              (decodeBHist (encodeBHist probability)) (decodeBHist (encodeBHist evidence))) :=
        congrArg
          (fun row =>
            some (BeliefUp.mk prior row (decodeBHist (encodeBHist updateTrace))
              (decodeBHist (encodeBHist probability)) (decodeBHist (encodeBHist evidence))))
          (decode_encode_bhist observation)
      have hUpdateTrace :
          some (BeliefUp.mk prior observation (decodeBHist (encodeBHist updateTrace))
            (decodeBHist (encodeBHist probability)) (decodeBHist (encodeBHist evidence))) =
            some (BeliefUp.mk prior observation updateTrace
              (decodeBHist (encodeBHist probability)) (decodeBHist (encodeBHist evidence))) :=
        congrArg
          (fun row =>
            some (BeliefUp.mk prior observation row (decodeBHist (encodeBHist probability))
              (decodeBHist (encodeBHist evidence))))
          (decode_encode_bhist updateTrace)
      have hProbability :
          some (BeliefUp.mk prior observation updateTrace
            (decodeBHist (encodeBHist probability)) (decodeBHist (encodeBHist evidence))) =
            some (BeliefUp.mk prior observation updateTrace probability
              (decodeBHist (encodeBHist evidence))) :=
        congrArg
          (fun row =>
            some (BeliefUp.mk prior observation updateTrace row
              (decodeBHist (encodeBHist evidence))))
          (decode_encode_bhist probability)
      have hEvidence :
          some (BeliefUp.mk prior observation updateTrace probability
            (decodeBHist (encodeBHist evidence))) =
            some (BeliefUp.mk prior observation updateTrace probability evidence) :=
        congrArg
          (fun row => some (BeliefUp.mk prior observation updateTrace probability row))
          (decode_encode_bhist evidence)
      exact Eq.trans hPrior (Eq.trans hObservation
        (Eq.trans hUpdateTrace (Eq.trans hProbability hEvidence)))

theorem beliefToEventFlow_injective {x y : BeliefUp} :
    beliefToEventFlow x = beliefToEventFlow y → x = y := by
  intro heq
  have hread : beliefFromEventFlow (beliefToEventFlow x) = beliefFromEventFlow (beliefToEventFlow y) :=
    congrArg beliefFromEventFlow heq
  exact Option.some.inj (Eq.trans (belief_round_trip x).symm (Eq.trans hread (belief_round_trip y)))

instance beliefBHistCarrier : BHistCarrier BeliefUp where
  toEventFlow := beliefToEventFlow
  fromEventFlow := beliefFromEventFlow

instance beliefChapterTasteGate : ChapterTasteGate BeliefUp where
  round_trip := by
    intro x
    change beliefFromEventFlow (beliefToEventFlow x) = some x
    exact belief_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (beliefToEventFlow_injective heq)

theorem BeliefTasteGate_carrier_recognition :
    (forall x : BeliefUp, beliefFromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
      (forall x y : BeliefUp,
        BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) := by
  constructor
  · intro x
    change beliefFromEventFlow (beliefToEventFlow x) = some x
    exact belief_round_trip x
  · intro x y heq
    exact beliefToEventFlow_injective heq

/-- Public alias matching the audit-gate marker
`BEDC.Derived.BeliefUp.taste_gate`. -/
def taste_gate : ChapterTasteGate BeliefUp := beliefChapterTasteGate

end BEDC.Derived.BeliefUp
