import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnwitnessedExistenceClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite unwitnessed-existence closure packet with the ten displayed BEDC rows. -/
inductive UnwitnessedExistenceClosureUp : Type where
  | mk :
      (term type proposition classifier stability ledger handoff transports pkg name : BHist) →
      UnwitnessedExistenceClosureUp
  deriving DecidableEq

private def UnwitnessedExistenceClosureUp_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: UnwitnessedExistenceClosureUp_encodeBHist h
  | BHist.e1 h => BMark.b1 :: UnwitnessedExistenceClosureUp_encodeBHist h

private def UnwitnessedExistenceClosureUp_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (UnwitnessedExistenceClosureUp_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (UnwitnessedExistenceClosureUp_decodeBHist tail)

private theorem UnwitnessedExistenceClosureUp_decodeEncodeBHist :
    ∀ h : BHist,
      UnwitnessedExistenceClosureUp_decodeBHist
          (UnwitnessedExistenceClosureUp_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def UnwitnessedExistenceClosureUp_toEventFlow :
    UnwitnessedExistenceClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UnwitnessedExistenceClosureUp.mk term type proposition classifier stability ledger handoff
      transports pkg name =>
      [[BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist term,
        [BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist type,
        [BMark.b1, BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist proposition,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist pkg,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        UnwitnessedExistenceClosureUp_encodeBHist name]

private def UnwitnessedExistenceClosureUp_fromEventFlow :
    EventFlow → Option UnwitnessedExistenceClosureUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | term :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | type :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | proposition :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | stability :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | handoff :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transports :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | pkg :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (UnwitnessedExistenceClosureUp.mk
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            term)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            type)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            proposition)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            classifier)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            stability)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            ledger)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            handoff)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            transports)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            pkg)
                                                                                          (UnwitnessedExistenceClosureUp_decodeBHist
                                                                                            name))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem UnwitnessedExistenceClosureUp_roundTrip :
    ∀ x : UnwitnessedExistenceClosureUp,
      UnwitnessedExistenceClosureUp_fromEventFlow
          (UnwitnessedExistenceClosureUp_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term type proposition classifier stability ledger handoff transports pkg name =>
      change
        some
          (UnwitnessedExistenceClosureUp.mk
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist term))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist type))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist proposition))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist classifier))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist stability))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist ledger))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist handoff))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist transports))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist pkg))
            (UnwitnessedExistenceClosureUp_decodeBHist
              (UnwitnessedExistenceClosureUp_encodeBHist name))) =
          some
            (UnwitnessedExistenceClosureUp.mk term type proposition classifier stability ledger
              handoff transports pkg name)
      rw [UnwitnessedExistenceClosureUp_decodeEncodeBHist term,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist type,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist proposition,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist classifier,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist stability,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist ledger,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist handoff,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist transports,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist pkg,
        UnwitnessedExistenceClosureUp_decodeEncodeBHist name]

private theorem UnwitnessedExistenceClosureUp_toEventFlowInjective
    {x y : UnwitnessedExistenceClosureUp} :
    UnwitnessedExistenceClosureUp_toEventFlow x =
        UnwitnessedExistenceClosureUp_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      UnwitnessedExistenceClosureUp_fromEventFlow
          (UnwitnessedExistenceClosureUp_toEventFlow x) =
        UnwitnessedExistenceClosureUp_fromEventFlow
          (UnwitnessedExistenceClosureUp_toEventFlow y) :=
    congrArg UnwitnessedExistenceClosureUp_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UnwitnessedExistenceClosureUp_roundTrip x).symm
      (Eq.trans hread (UnwitnessedExistenceClosureUp_roundTrip y)))

instance UnwitnessedExistenceClosureUp_bhistCarrier :
    BHistCarrier UnwitnessedExistenceClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := UnwitnessedExistenceClosureUp_toEventFlow
  fromEventFlow := UnwitnessedExistenceClosureUp_fromEventFlow

instance UnwitnessedExistenceClosureUp_chapterTasteGate :
    ChapterTasteGate UnwitnessedExistenceClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      UnwitnessedExistenceClosureUp_fromEventFlow
          (UnwitnessedExistenceClosureUp_toEventFlow x) =
        some x
    exact UnwitnessedExistenceClosureUp_roundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UnwitnessedExistenceClosureUp_toEventFlowInjective heq)

end BEDC.Derived.UnwitnessedExistenceClosureUp
