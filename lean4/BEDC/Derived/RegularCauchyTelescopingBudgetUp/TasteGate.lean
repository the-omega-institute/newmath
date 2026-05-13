import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTelescopingBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTelescopingBudgetUp : Type where
  | mk : (E W D R S T H C P N : BHist) → RegularCauchyTelescopingBudgetUp
  deriving DecidableEq

def regularCauchyTelescopingBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTelescopingBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTelescopingBudgetEncodeBHist h

def regularCauchyTelescopingBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTelescopingBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTelescopingBudgetDecodeBHist tail)

private theorem regularCauchyTelescopingBudgetDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTelescopingBudgetDecodeBHist
        (regularCauchyTelescopingBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTelescopingBudgetToEventFlow :
    RegularCauchyTelescopingBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTelescopingBudgetUp.mk E W D R S T H C P N =>
      [[BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist E,
        [BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyTelescopingBudgetEncodeBHist N]

def regularCauchyTelescopingBudgetFromEventFlow :
    EventFlow → Option RegularCauchyTelescopingBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | S :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | T :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (RegularCauchyTelescopingBudgetUp.mk
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist E)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist W)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist D)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist R)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist S)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist T)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist H)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist C)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist P)
                                                                                          (regularCauchyTelescopingBudgetDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem regularCauchyTelescopingBudget_round_trip :
    ∀ x : RegularCauchyTelescopingBudgetUp,
      regularCauchyTelescopingBudgetFromEventFlow
        (regularCauchyTelescopingBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E W D R S T H C P N =>
      change
        some
          (RegularCauchyTelescopingBudgetUp.mk
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist E))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist W))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist D))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist R))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist S))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist T))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist H))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist C))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist P))
            (regularCauchyTelescopingBudgetDecodeBHist
              (regularCauchyTelescopingBudgetEncodeBHist N))) =
          some (RegularCauchyTelescopingBudgetUp.mk E W D R S T H C P N)
      rw [regularCauchyTelescopingBudgetDecode_encode_bhist E,
        regularCauchyTelescopingBudgetDecode_encode_bhist W,
        regularCauchyTelescopingBudgetDecode_encode_bhist D,
        regularCauchyTelescopingBudgetDecode_encode_bhist R,
        regularCauchyTelescopingBudgetDecode_encode_bhist S,
        regularCauchyTelescopingBudgetDecode_encode_bhist T,
        regularCauchyTelescopingBudgetDecode_encode_bhist H,
        regularCauchyTelescopingBudgetDecode_encode_bhist C,
        regularCauchyTelescopingBudgetDecode_encode_bhist P,
        regularCauchyTelescopingBudgetDecode_encode_bhist N]

private theorem regularCauchyTelescopingBudgetToEventFlow_injective
    {x y : RegularCauchyTelescopingBudgetUp} :
    regularCauchyTelescopingBudgetToEventFlow x =
      regularCauchyTelescopingBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTelescopingBudgetFromEventFlow
          (regularCauchyTelescopingBudgetToEventFlow x) =
        regularCauchyTelescopingBudgetFromEventFlow
          (regularCauchyTelescopingBudgetToEventFlow y) :=
    congrArg regularCauchyTelescopingBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTelescopingBudget_round_trip x).symm
      (Eq.trans hread (regularCauchyTelescopingBudget_round_trip y)))

instance regularCauchyTelescopingBudgetBHistCarrier :
    BHistCarrier RegularCauchyTelescopingBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTelescopingBudgetToEventFlow
  fromEventFlow := regularCauchyTelescopingBudgetFromEventFlow

instance regularCauchyTelescopingBudgetChapterTasteGate :
    ChapterTasteGate RegularCauchyTelescopingBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTelescopingBudgetFromEventFlow
        (regularCauchyTelescopingBudgetToEventFlow x) = some x
    exact regularCauchyTelescopingBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTelescopingBudgetToEventFlow_injective heq)

instance regularCauchyTelescopingBudgetFieldFaithful :
    FieldFaithful RegularCauchyTelescopingBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RegularCauchyTelescopingBudgetUp.mk E W D R S T H C P N =>
        [E, W, D, R, S, T, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk E1 W1 D1 R1 S1 T1 H1 C1 P1 N1 =>
        cases y with
        | mk E2 W2 D2 R2 S2 T2 H2 C2 P2 N2 =>
            injection h with hE t1
            injection t1 with hW t2
            injection t2 with hD t3
            injection t3 with hR t4
            injection t4 with hS t5
            injection t5 with hT t6
            injection t6 with hH t7
            injection t7 with hC t8
            injection t8 with hP t9
            injection t9 with hN _
            cases hE
            cases hW
            cases hD
            cases hR
            cases hS
            cases hT
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

theorem RegularCauchyTelescopingBudgetTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyTelescopingBudgetDecodeBHist
        (regularCauchyTelescopingBudgetEncodeBHist h) = h) ∧
      (forall x : RegularCauchyTelescopingBudgetUp,
        regularCauchyTelescopingBudgetFromEventFlow
          (regularCauchyTelescopingBudgetToEventFlow x) = some x) ∧
        (forall x y : RegularCauchyTelescopingBudgetUp,
          regularCauchyTelescopingBudgetToEventFlow x =
            regularCauchyTelescopingBudgetToEventFlow y -> x = y) ∧
          regularCauchyTelescopingBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyTelescopingBudgetDecode_encode_bhist
  · constructor
    · exact regularCauchyTelescopingBudget_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyTelescopingBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyTelescopingBudgetUp
