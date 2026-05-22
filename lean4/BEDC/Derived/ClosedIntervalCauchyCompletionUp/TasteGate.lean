import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedIntervalCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedIntervalCauchyCompletionUp : Type where
  | mk (A B I S R D Q E H C P N : BHist) : ClosedIntervalCauchyCompletionUp
  deriving DecidableEq

def closedIntervalCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedIntervalCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedIntervalCauchyCompletionEncodeBHist h

def closedIntervalCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedIntervalCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedIntervalCauchyCompletionDecodeBHist tail)

private theorem closedIntervalCauchyCompletion_decode_encode_bhist :
    ∀ h : BHist,
      closedIntervalCauchyCompletionDecodeBHist
          (closedIntervalCauchyCompletionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem closedIntervalCauchyCompletion_mk_congr
    {A A' B B' I I' S S' R R' D D' Q Q' E E' H H' C C' P P' N N' : BHist}
    (hA : A' = A) (hB : B' = B) (hI : I' = I) (hS : S' = S)
    (hR : R' = R) (hD : D' = D) (hQ : Q' = Q) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    ClosedIntervalCauchyCompletionUp.mk A' B' I' S' R' D' Q' E' H' C' P' N' =
      ClosedIntervalCauchyCompletionUp.mk A B I S R D Q E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hI
  cases hS
  cases hR
  cases hD
  cases hQ
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def closedIntervalCauchyCompletionFields :
    ClosedIntervalCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedIntervalCauchyCompletionUp.mk A B I S R D Q E H C P N =>
      [A, B, I, S, R, D, Q, E, H, C, P, N]

def closedIntervalCauchyCompletionToEventFlow :
    ClosedIntervalCauchyCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (closedIntervalCauchyCompletionFields x).map
      closedIntervalCauchyCompletionEncodeBHist

def closedIntervalCauchyCompletionFromEventFlow :
    EventFlow → Option ClosedIntervalCauchyCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | I :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | H :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | N :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (ClosedIntervalCauchyCompletionUp.mk
                                                          (closedIntervalCauchyCompletionDecodeBHist A)
                                                          (closedIntervalCauchyCompletionDecodeBHist B)
                                                          (closedIntervalCauchyCompletionDecodeBHist I)
                                                          (closedIntervalCauchyCompletionDecodeBHist S)
                                                          (closedIntervalCauchyCompletionDecodeBHist R)
                                                          (closedIntervalCauchyCompletionDecodeBHist D)
                                                          (closedIntervalCauchyCompletionDecodeBHist Q)
                                                          (closedIntervalCauchyCompletionDecodeBHist E)
                                                          (closedIntervalCauchyCompletionDecodeBHist H)
                                                          (closedIntervalCauchyCompletionDecodeBHist C)
                                                          (closedIntervalCauchyCompletionDecodeBHist P)
                                                          (closedIntervalCauchyCompletionDecodeBHist N))
                                                  | _ :: _ => none

private theorem closedIntervalCauchyCompletion_round_trip :
    ∀ x : ClosedIntervalCauchyCompletionUp,
      closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B I S R D Q E H C P N =>
      exact
        congrArg some
          (closedIntervalCauchyCompletion_mk_congr
            (closedIntervalCauchyCompletion_decode_encode_bhist A)
            (closedIntervalCauchyCompletion_decode_encode_bhist B)
            (closedIntervalCauchyCompletion_decode_encode_bhist I)
            (closedIntervalCauchyCompletion_decode_encode_bhist S)
            (closedIntervalCauchyCompletion_decode_encode_bhist R)
            (closedIntervalCauchyCompletion_decode_encode_bhist D)
            (closedIntervalCauchyCompletion_decode_encode_bhist Q)
            (closedIntervalCauchyCompletion_decode_encode_bhist E)
            (closedIntervalCauchyCompletion_decode_encode_bhist H)
            (closedIntervalCauchyCompletion_decode_encode_bhist C)
            (closedIntervalCauchyCompletion_decode_encode_bhist P)
            (closedIntervalCauchyCompletion_decode_encode_bhist N))

private theorem closedIntervalCauchyCompletionToEventFlow_injective
    {x y : ClosedIntervalCauchyCompletionUp} :
    closedIntervalCauchyCompletionToEventFlow x =
        closedIntervalCauchyCompletionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow x) =
        closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow y) :=
    congrArg closedIntervalCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedIntervalCauchyCompletion_round_trip x).symm
      (Eq.trans hread (closedIntervalCauchyCompletion_round_trip y)))

instance closedIntervalCauchyCompletionBHistCarrier :
    BHistCarrier ClosedIntervalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedIntervalCauchyCompletionToEventFlow
  fromEventFlow := closedIntervalCauchyCompletionFromEventFlow

instance closedIntervalCauchyCompletionChapterTasteGate :
    ChapterTasteGate ClosedIntervalCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedIntervalCauchyCompletionFromEventFlow
          (closedIntervalCauchyCompletionToEventFlow x) =
        some x
    exact closedIntervalCauchyCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedIntervalCauchyCompletionToEventFlow_injective heq)

namespace TasteGate

theorem ClosedIntervalCauchyCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      closedIntervalCauchyCompletionDecodeBHist
          (closedIntervalCauchyCompletionEncodeBHist h) =
        h) ∧
      (∀ x : ClosedIntervalCauchyCompletionUp,
        closedIntervalCauchyCompletionFromEventFlow
            (closedIntervalCauchyCompletionToEventFlow x) =
          some x) ∧
        (∀ x y : ClosedIntervalCauchyCompletionUp,
          closedIntervalCauchyCompletionToEventFlow x =
              closedIntervalCauchyCompletionToEventFlow y →
            x = y) ∧
          closedIntervalCauchyCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact closedIntervalCauchyCompletion_decode_encode_bhist
  · constructor
    · exact closedIntervalCauchyCompletion_round_trip
    · constructor
      · intro x y heq
        exact closedIntervalCauchyCompletionToEventFlow_injective heq
      · rfl

end TasteGate

end BEDC.Derived.ClosedIntervalCauchyCompletionUp
