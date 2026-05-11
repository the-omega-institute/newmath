import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonodromyUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonodromyUp : Type where
  | mk : (loop base localSystem returned ledger transports provenance : BHist) → MonodromyUp

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

private def monodromyToEventFlow : MonodromyUp → EventFlow
  | MonodromyUp.mk loop base localSystem returned ledger transports provenance =>
      [[BMark.b0], encodeBHist loop,
        [BMark.b1, BMark.b0], encodeBHist base,
        [BMark.b1, BMark.b1, BMark.b0], encodeBHist localSystem,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist returned,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist provenance]

private def monodromyFromEventFlow : EventFlow → Option MonodromyUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | loop :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | base :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | localSystem :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | returned :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | ledger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (MonodromyUp.mk
                                                                  (decodeBHist loop)
                                                                  (decodeBHist base)
                                                                  (decodeBHist localSystem)
                                                                  (decodeBHist returned)
                                                                  (decodeBHist ledger)
                                                                  (decodeBHist transports)
                                                                  (decodeBHist provenance))
                                                          | _ :: _ => none

private theorem monodromy_round_trip :
    ∀ x : MonodromyUp, monodromyFromEventFlow (monodromyToEventFlow x) = some x := by
  intro x
  cases x with
  | mk loop base localSystem returned ledger transports provenance =>
      change
        some (MonodromyUp.mk (decodeBHist (encodeBHist loop))
          (decodeBHist (encodeBHist base)) (decodeBHist (encodeBHist localSystem))
          (decodeBHist (encodeBHist returned)) (decodeBHist (encodeBHist ledger))
          (decodeBHist (encodeBHist transports)) (decodeBHist (encodeBHist provenance))) =
          some (MonodromyUp.mk loop base localSystem returned ledger transports provenance)
      rw [decode_encode_bhist loop, decode_encode_bhist base,
        decode_encode_bhist localSystem, decode_encode_bhist returned,
        decode_encode_bhist ledger, decode_encode_bhist transports,
        decode_encode_bhist provenance]

private theorem monodromyToEventFlow_injective {x y : MonodromyUp} :
    monodromyToEventFlow x = monodromyToEventFlow y → x = y := by
  intro heq
  have hread :
      monodromyFromEventFlow (monodromyToEventFlow x) =
        monodromyFromEventFlow (monodromyToEventFlow y) :=
    congrArg monodromyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (monodromy_round_trip x).symm (Eq.trans hread (monodromy_round_trip y)))

instance monodromyBHistCarrier : BHistCarrier MonodromyUp where
  toEventFlow := monodromyToEventFlow
  fromEventFlow := monodromyFromEventFlow

instance monodromyChapterTasteGate : ChapterTasteGate MonodromyUp where
  round_trip := by
    intro x
    change monodromyFromEventFlow (monodromyToEventFlow x) = some x
    exact monodromy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (monodromyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MonodromyUp := monodromyChapterTasteGate

end BEDC.Derived.MonodromyUp
