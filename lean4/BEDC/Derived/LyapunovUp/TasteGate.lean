import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LyapunovUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LyapunovUp : Type where
  | mk :
      (state transition quadratic positive decrease transports routes provenance name : BHist) →
        LyapunovUp

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

private def lyapunovToEventFlow : LyapunovUp → EventFlow
  | LyapunovUp.mk state transition quadratic positive decrease transports routes provenance name =>
      [[BMark.b0], encodeBHist state,
        [BMark.b1, BMark.b0], encodeBHist transition,
        [BMark.b1, BMark.b1, BMark.b0], encodeBHist quadratic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist positive,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0], encodeBHist decrease,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          encodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
          encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
          encodeBHist name]

private def lyapunovFromEventFlow : EventFlow → Option LyapunovUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | state :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | transition :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | quadratic :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | positive :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | decrease :: rest9 =>
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
                                                      | routes :: rest13 =>
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
                                                                                (LyapunovUp.mk
                                                                                  (decodeBHist state)
                                                                                  (decodeBHist transition)
                                                                                  (decodeBHist quadratic)
                                                                                  (decodeBHist positive)
                                                                                  (decodeBHist decrease)
                                                                                  (decodeBHist transports)
                                                                                  (decodeBHist routes)
                                                                                  (decodeBHist provenance)
                                                                                  (decodeBHist name))
                                                                          | _ :: _ => none

private theorem lyapunov_round_trip :
    ∀ x : LyapunovUp, lyapunovFromEventFlow (lyapunovToEventFlow x) = some x := by
  intro x
  cases x with
  | mk state transition quadratic positive decrease transports routes provenance name =>
      change
        some (LyapunovUp.mk (decodeBHist (encodeBHist state))
          (decodeBHist (encodeBHist transition)) (decodeBHist (encodeBHist quadratic))
          (decodeBHist (encodeBHist positive)) (decodeBHist (encodeBHist decrease))
          (decodeBHist (encodeBHist transports)) (decodeBHist (encodeBHist routes))
          (decodeBHist (encodeBHist provenance)) (decodeBHist (encodeBHist name))) =
          some
            (LyapunovUp.mk state transition quadratic positive decrease transports routes
              provenance name)
      rw [decode_encode_bhist state, decode_encode_bhist transition,
        decode_encode_bhist quadratic, decode_encode_bhist positive,
        decode_encode_bhist decrease, decode_encode_bhist transports,
        decode_encode_bhist routes, decode_encode_bhist provenance, decode_encode_bhist name]

private theorem lyapunovToEventFlow_injective {x y : LyapunovUp} :
    lyapunovToEventFlow x = lyapunovToEventFlow y → x = y := by
  intro heq
  have hread :
      lyapunovFromEventFlow (lyapunovToEventFlow x) =
        lyapunovFromEventFlow (lyapunovToEventFlow y) :=
    congrArg lyapunovFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lyapunov_round_trip x).symm (Eq.trans hread (lyapunov_round_trip y)))

instance lyapunovBHistCarrier : BHistCarrier LyapunovUp where
  toEventFlow := lyapunovToEventFlow
  fromEventFlow := lyapunovFromEventFlow

instance lyapunovChapterTasteGate : ChapterTasteGate LyapunovUp where
  round_trip := by
    intro x
    change lyapunovFromEventFlow (lyapunovToEventFlow x) = some x
    exact lyapunov_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lyapunovToEventFlow_injective heq)

def taste_gate : ChapterTasteGate LyapunovUp := lyapunovChapterTasteGate

end BEDC.Derived.LyapunovUp
