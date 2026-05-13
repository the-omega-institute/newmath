import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalRegularLimitBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalRegularLimitBudgetUp : Type where
  | mk :
      (q w r e h c p n : BHist) →
      CofinalRegularLimitBudgetUp
  deriving DecidableEq

def cofinalRegularLimitBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalRegularLimitBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalRegularLimitBudgetEncodeBHist h

def cofinalRegularLimitBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalRegularLimitBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalRegularLimitBudgetDecodeBHist tail)

private theorem cofinalRegularLimitBudget_decode_encode_bhist :
    ∀ h : BHist,
      cofinalRegularLimitBudgetDecodeBHist
        (cofinalRegularLimitBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hist
  induction hist with
  | Empty =>
      rfl
  | e0 hist ih =>
      exact congrArg BHist.e0 ih
  | e1 hist ih =>
      exact congrArg BHist.e1 ih

private theorem cofinalRegularLimitBudget_mk_congr
    {q q' w w' r r' e e' h h' c c' p p' n n' : BHist}
    (hq : q' = q)
    (hw : w' = w)
    (hr : r' = r)
    (he : e' = e)
    (hh : h' = h)
    (hc : c' = c)
    (hp : p' = p)
    (hn : n' = n) :
    CofinalRegularLimitBudgetUp.mk q' w' r' e' h' c' p' n' =
      CofinalRegularLimitBudgetUp.mk q w r e h c p n := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hq
  cases hw
  cases hr
  cases he
  cases hh
  cases hc
  cases hp
  cases hn
  rfl

def cofinalRegularLimitBudgetToEventFlow : CofinalRegularLimitBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalRegularLimitBudgetUp.mk q w r e h c p n =>
      [[BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist q,
        [BMark.b1, BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist e,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalRegularLimitBudgetEncodeBHist n]

def cofinalRegularLimitBudgetFromEventFlow :
    EventFlow → Option CofinalRegularLimitBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | q :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | w :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | r :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | e :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | h :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | c :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | p :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | n :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (CofinalRegularLimitBudgetUp.mk
                                                                          (cofinalRegularLimitBudgetDecodeBHist q)
                                                                          (cofinalRegularLimitBudgetDecodeBHist w)
                                                                          (cofinalRegularLimitBudgetDecodeBHist r)
                                                                          (cofinalRegularLimitBudgetDecodeBHist e)
                                                                          (cofinalRegularLimitBudgetDecodeBHist h)
                                                                          (cofinalRegularLimitBudgetDecodeBHist c)
                                                                          (cofinalRegularLimitBudgetDecodeBHist p)
                                                                          (cofinalRegularLimitBudgetDecodeBHist n))
                                                                  | _ :: _ => none

private theorem cofinalRegularLimitBudget_round_trip :
    ∀ x : CofinalRegularLimitBudgetUp,
      cofinalRegularLimitBudgetFromEventFlow
        (cofinalRegularLimitBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q w r e h c p n =>
      change
        some
          (CofinalRegularLimitBudgetUp.mk
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist q))
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist w))
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist r))
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist e))
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist h))
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist c))
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist p))
            (cofinalRegularLimitBudgetDecodeBHist
              (cofinalRegularLimitBudgetEncodeBHist n))) =
          some (CofinalRegularLimitBudgetUp.mk q w r e h c p n)
      exact
        congrArg some
          (cofinalRegularLimitBudget_mk_congr
            (cofinalRegularLimitBudget_decode_encode_bhist q)
            (cofinalRegularLimitBudget_decode_encode_bhist w)
            (cofinalRegularLimitBudget_decode_encode_bhist r)
            (cofinalRegularLimitBudget_decode_encode_bhist e)
            (cofinalRegularLimitBudget_decode_encode_bhist h)
            (cofinalRegularLimitBudget_decode_encode_bhist c)
            (cofinalRegularLimitBudget_decode_encode_bhist p)
            (cofinalRegularLimitBudget_decode_encode_bhist n))

private theorem cofinalRegularLimitBudgetToEventFlow_injective
    {x y : CofinalRegularLimitBudgetUp} :
    cofinalRegularLimitBudgetToEventFlow x =
      cofinalRegularLimitBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalRegularLimitBudgetFromEventFlow
          (cofinalRegularLimitBudgetToEventFlow x) =
        cofinalRegularLimitBudgetFromEventFlow
          (cofinalRegularLimitBudgetToEventFlow y) :=
    congrArg cofinalRegularLimitBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalRegularLimitBudget_round_trip x).symm
      (Eq.trans hread (cofinalRegularLimitBudget_round_trip y)))

instance cofinalRegularLimitBudgetBHistCarrier :
    BHistCarrier CofinalRegularLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalRegularLimitBudgetToEventFlow
  fromEventFlow := cofinalRegularLimitBudgetFromEventFlow

instance cofinalRegularLimitBudgetChapterTasteGate :
    ChapterTasteGate CofinalRegularLimitBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cofinalRegularLimitBudgetFromEventFlow
        (cofinalRegularLimitBudgetToEventFlow x) = some x
    exact cofinalRegularLimitBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalRegularLimitBudgetToEventFlow_injective heq)

instance cofinalRegularLimitBudgetFieldFaithful :
    FieldFaithful CofinalRegularLimitBudgetUp where
  fields
    | CofinalRegularLimitBudgetUp.mk q w r e h c p n => [q, w, r, e, h, c, p, n]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk q w r e h c p n =>
        cases y with
        | mk q' w' r' e' h' c' p' n' =>
            cases hfields
            rfl

def taste_gate : ChapterTasteGate CofinalRegularLimitBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem CofinalRegularLimitBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cofinalRegularLimitBudgetDecodeBHist
        (cofinalRegularLimitBudgetEncodeBHist h) = h) ∧
      (∀ x : CofinalRegularLimitBudgetUp,
        cofinalRegularLimitBudgetFromEventFlow
          (cofinalRegularLimitBudgetToEventFlow x) = some x) ∧
        (∀ x y : CofinalRegularLimitBudgetUp,
          cofinalRegularLimitBudgetToEventFlow x =
            cofinalRegularLimitBudgetToEventFlow y → x = y) ∧
          cofinalRegularLimitBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cofinalRegularLimitBudget_decode_encode_bhist
  · constructor
    · exact cofinalRegularLimitBudget_round_trip
    · constructor
      · intro x y heq
        exact cofinalRegularLimitBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.CofinalRegularLimitBudgetUp
