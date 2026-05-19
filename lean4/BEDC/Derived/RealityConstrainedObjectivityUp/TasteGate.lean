import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedObjectivityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedObjectivityUp : Type where
  | mk :
      (history anchor invariant fit reflection approximation audit ledger name : BHist) →
      RealityConstrainedObjectivityUp
  deriving DecidableEq

def RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist h

def RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
          (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist h) =
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

def RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow :
    RealityConstrainedObjectivityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedObjectivityUp.mk history anchor invariant fit reflection approximation audit
      ledger name =>
      [[BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist history,
        [BMark.b1, BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist anchor,
        [BMark.b1, BMark.b1, BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist invariant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist fit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist reflection,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
          approximation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist name]

def RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option RealityConstrainedObjectivityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | anchor :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | invariant :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | fit :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | reflection :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | approximation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | audit :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | ledger :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RealityConstrainedObjectivityUp.mk
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    history)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    anchor)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    invariant)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    fit)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    reflection)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    approximation)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    audit)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    ledger)
                                                                                  (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem RealityConstrainedObjectivityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealityConstrainedObjectivityUp,
      RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fromEventFlow
          (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history anchor invariant fit reflection approximation audit ledger name =>
      change
        some
            (RealityConstrainedObjectivityUp.mk
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  history))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  anchor))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  invariant))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  fit))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  reflection))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  approximation))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  audit))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  ledger))
              (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
                (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
                  name))) =
          some
            (RealityConstrainedObjectivityUp.mk history anchor invariant fit reflection
              approximation audit ledger name)
      rw [RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode history,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode anchor,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode invariant,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode fit,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode reflection,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode approximation,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode audit,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode ledger,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode name]

private theorem RealityConstrainedObjectivityTasteGate_single_carrier_alignment_injective
    {x y : RealityConstrainedObjectivityUp} :
    RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow x =
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fromEventFlow
          (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow x) =
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fromEventFlow
          (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_round_trip y)))

private def RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fields :
    RealityConstrainedObjectivityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedObjectivityUp.mk history anchor invariant fit reflection approximation audit
      ledger name =>
      [history, anchor, invariant, fit, reflection, approximation, audit, ledger, name]

private theorem RealityConstrainedObjectivityTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : RealityConstrainedObjectivityUp,
      RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fields x =
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk history anchor invariant fit reflection approximation audit ledger name =>
      cases y with
      | mk history' anchor' invariant' fit' reflection' approximation' audit' ledger' name' =>
          cases hfields
          rfl

instance realityConstrainedObjectivityBHistCarrier :
    BHistCarrier RealityConstrainedObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow :=
    RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fromEventFlow

instance realityConstrainedObjectivityChapterTasteGate :
    ChapterTasteGate RealityConstrainedObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fromEventFlow
          (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact RealityConstrainedObjectivityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_injective heq)

instance realityConstrainedObjectivityFieldFaithful :
    FieldFaithful RealityConstrainedObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fields
  field_faithful :=
    RealityConstrainedObjectivityTasteGate_single_carrier_alignment_field_faithful

instance realityConstrainedObjectivityNontrivial :
    Nontrivial RealityConstrainedObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedObjectivityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedObjectivityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedObjectivityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedObjectivityChapterTasteGate

theorem RealityConstrainedObjectivityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decodeBHist
          (RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      (∀ x y : RealityConstrainedObjectivityUp,
        RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fields x =
          RealityConstrainedObjectivityTasteGate_single_carrier_alignment_fields y →
        x = y) ∧
        Nonempty (FieldFaithful RealityConstrainedObjectivityUp) ∧
          Nonempty (Nontrivial RealityConstrainedObjectivityUp) ∧
            RealityConstrainedObjectivityTasteGate_single_carrier_alignment_encodeBHist
              BHist.Empty =
              ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact RealityConstrainedObjectivityTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RealityConstrainedObjectivityTasteGate_single_carrier_alignment_field_faithful
    · constructor
      · exact ⟨realityConstrainedObjectivityFieldFaithful⟩
      · constructor
        · exact ⟨realityConstrainedObjectivityNontrivial⟩
        · rfl

theorem RealityConstrainedObjectivityCarrier_anchor_stability
    {H A I F R T P L N anchorRoute invariantRead ledgerRead : BHist} :
    UnaryHistory A →
      UnaryHistory I →
        UnaryHistory L →
          Cont A I anchorRoute →
            Cont anchorRoute L invariantRead →
              Cont I L ledgerRead →
                ∃ O : RealityConstrainedObjectivityUp,
                  O = RealityConstrainedObjectivityUp.mk H A I F R T P L N ∧
                    UnaryHistory anchorRoute ∧
                      UnaryHistory invariantRead ∧
                        UnaryHistory ledgerRead ∧
                          Cont A I anchorRoute ∧
                            Cont anchorRoute L invariantRead ∧ Cont I L ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro anchorUnary invariantUnary ledgerUnary anchorRouteCont invariantRouteCont
    ledgerRouteCont
  have anchorRouteUnary : UnaryHistory anchorRoute :=
    unary_cont_closed anchorUnary invariantUnary anchorRouteCont
  have invariantReadUnary : UnaryHistory invariantRead :=
    unary_cont_closed anchorRouteUnary ledgerUnary invariantRouteCont
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed invariantUnary ledgerUnary ledgerRouteCont
  exact
    ⟨RealityConstrainedObjectivityUp.mk H A I F R T P L N, rfl, anchorRouteUnary,
      invariantReadUnary, ledgerReadUnary, anchorRouteCont, invariantRouteCont,
      ledgerRouteCont⟩

end BEDC.Derived.RealityConstrainedObjectivityUp
