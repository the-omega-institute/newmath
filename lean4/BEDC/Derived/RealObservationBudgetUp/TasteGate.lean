import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealObservationBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealObservationBudgetUp : Type where
  | mk : (E W D R S H C P N : BHist) → RealObservationBudgetUp
  deriving DecidableEq

def realObservationBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realObservationBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realObservationBudgetEncodeBHist h

def realObservationBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realObservationBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realObservationBudgetDecodeBHist tail)

private theorem realObservationBudgetDecode_encode_bhist :
    ∀ h : BHist, realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realObservationBudget_mk_congr
    {E E' W W' D D' R R' S S' H H' C C' P P' N N' : BHist}
    (hE : E' = E)
    (hW : W' = W)
    (hD : D' = D)
    (hR : R' = R)
    (hS : S' = S)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N) :
    RealObservationBudgetUp.mk E' W' D' R' S' H' C' P' N' =
      RealObservationBudgetUp.mk E W D R S H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hE
  cases hW
  cases hD
  cases hR
  cases hS
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def realObservationBudgetToEventFlow : RealObservationBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealObservationBudgetUp.mk E W D R S H C P N =>
      [[BMark.b0],
        realObservationBudgetEncodeBHist E,
        [BMark.b1, BMark.b0],
        realObservationBudgetEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        realObservationBudgetEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realObservationBudgetEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realObservationBudgetEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realObservationBudgetEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realObservationBudgetEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realObservationBudgetEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realObservationBudgetEncodeBHist N]

def realObservationBudgetFromEventFlow : EventFlow → Option RealObservationBudgetUp
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
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (RealObservationBudgetUp.mk
                                                                                  (realObservationBudgetDecodeBHist E)
                                                                                  (realObservationBudgetDecodeBHist W)
                                                                                  (realObservationBudgetDecodeBHist D)
                                                                                  (realObservationBudgetDecodeBHist R)
                                                                                  (realObservationBudgetDecodeBHist S)
                                                                                  (realObservationBudgetDecodeBHist H)
                                                                                  (realObservationBudgetDecodeBHist C)
                                                                                  (realObservationBudgetDecodeBHist P)
                                                                                  (realObservationBudgetDecodeBHist N))
                                                                          | _ :: _ => none

private theorem realObservationBudget_round_trip :
    ∀ x : RealObservationBudgetUp,
      realObservationBudgetFromEventFlow (realObservationBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E W D R S H C P N =>
      change
        some
          (RealObservationBudgetUp.mk
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist E))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist W))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist D))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist R))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist S))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist H))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist C))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist P))
            (realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist N))) =
          some (RealObservationBudgetUp.mk E W D R S H C P N)
      exact
        congrArg some
          (realObservationBudget_mk_congr
            (realObservationBudgetDecode_encode_bhist E)
            (realObservationBudgetDecode_encode_bhist W)
            (realObservationBudgetDecode_encode_bhist D)
            (realObservationBudgetDecode_encode_bhist R)
            (realObservationBudgetDecode_encode_bhist S)
            (realObservationBudgetDecode_encode_bhist H)
            (realObservationBudgetDecode_encode_bhist C)
            (realObservationBudgetDecode_encode_bhist P)
            (realObservationBudgetDecode_encode_bhist N))

private theorem realObservationBudgetToEventFlow_injective {x y : RealObservationBudgetUp} :
    realObservationBudgetToEventFlow x = realObservationBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realObservationBudgetFromEventFlow (realObservationBudgetToEventFlow x) =
        realObservationBudgetFromEventFlow (realObservationBudgetToEventFlow y) :=
    congrArg realObservationBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realObservationBudget_round_trip x).symm
      (Eq.trans hread (realObservationBudget_round_trip y)))

instance realObservationBudgetBHistCarrier : BHistCarrier RealObservationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realObservationBudgetToEventFlow
  fromEventFlow := realObservationBudgetFromEventFlow

instance realObservationBudgetChapterTasteGate : ChapterTasteGate RealObservationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realObservationBudgetFromEventFlow (realObservationBudgetToEventFlow x) = some x
    exact realObservationBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realObservationBudgetToEventFlow_injective heq)

theorem RealObservationBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist, realObservationBudgetDecodeBHist (realObservationBudgetEncodeBHist h) = h) ∧
      (∀ x : RealObservationBudgetUp,
        realObservationBudgetFromEventFlow (realObservationBudgetToEventFlow x) = some x) ∧
        (∀ x y : RealObservationBudgetUp,
          realObservationBudgetToEventFlow x = realObservationBudgetToEventFlow y → x = y) ∧
          realObservationBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realObservationBudgetDecode_encode_bhist
  · constructor
    · exact realObservationBudget_round_trip
    · constructor
      · intro x y heq
        exact realObservationBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.RealObservationBudgetUp
