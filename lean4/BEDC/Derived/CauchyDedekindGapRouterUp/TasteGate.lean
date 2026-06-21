import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDedekindGapRouterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDedekindGapRouterUp : Type where
  | mk (D S R E L B J H C P N : BHist) : CauchyDedekindGapRouterUp
  deriving DecidableEq

def cauchyDedekindGapRouterEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDedekindGapRouterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDedekindGapRouterEncodeBHist h

def cauchyDedekindGapRouterDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDedekindGapRouterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDedekindGapRouterDecodeBHist tail)

theorem CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      cauchyDedekindGapRouterDecodeBHist
        (cauchyDedekindGapRouterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CauchyDedekindGapRouterTasteGate_single_carrier_alignment_some_mk
    {D S R E L B J H C P N D' S' R' E' L' B' J' H' C' P' N' : BHist}
    (hD : D' = D) (hS : S' = S) (hR : R' = R) (hE : E' = E) (hL : L' = L)
    (hB : B' = B) (hJ : J' = J) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    some (CauchyDedekindGapRouterUp.mk D' S' R' E' L' B' J' H' C' P' N') =
      some (CauchyDedekindGapRouterUp.mk D S R E L B J H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hS
  cases hR
  cases hE
  cases hL
  cases hB
  cases hJ
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def cauchyDedekindGapRouterFields : CauchyDedekindGapRouterUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDedekindGapRouterUp.mk D S R E L B J H C P N =>
      [D, S, R, E, L, B, J, H, C, P, N]

def cauchyDedekindGapRouterToEventFlow : CauchyDedekindGapRouterUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyDedekindGapRouterFields x).map cauchyDedekindGapRouterEncodeBHist

def cauchyDedekindGapRouterFromEventFlow :
    EventFlow -> Option CauchyDedekindGapRouterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | B :: rest5 =>
                          match rest5 with
                          | [] => none
                          | J :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (CauchyDedekindGapRouterUp.mk
                                                      (cauchyDedekindGapRouterDecodeBHist D)
                                                      (cauchyDedekindGapRouterDecodeBHist S)
                                                      (cauchyDedekindGapRouterDecodeBHist R)
                                                      (cauchyDedekindGapRouterDecodeBHist E)
                                                      (cauchyDedekindGapRouterDecodeBHist L)
                                                      (cauchyDedekindGapRouterDecodeBHist B)
                                                      (cauchyDedekindGapRouterDecodeBHist J)
                                                      (cauchyDedekindGapRouterDecodeBHist H)
                                                      (cauchyDedekindGapRouterDecodeBHist C)
                                                      (cauchyDedekindGapRouterDecodeBHist P)
                                                      (cauchyDedekindGapRouterDecodeBHist N))
                                              | _ :: _ => none

theorem CauchyDedekindGapRouterTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyDedekindGapRouterUp,
      cauchyDedekindGapRouterFromEventFlow
        (cauchyDedekindGapRouterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E L B J H C P N =>
      exact
        CauchyDedekindGapRouterTasteGate_single_carrier_alignment_some_mk
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode D)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode S)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode R)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode E)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode L)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode B)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode J)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode H)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode C)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode P)
          (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode N)

theorem CauchyDedekindGapRouterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyDedekindGapRouterUp} :
    cauchyDedekindGapRouterToEventFlow x =
      cauchyDedekindGapRouterToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDedekindGapRouterFromEventFlow
          (cauchyDedekindGapRouterToEventFlow x) =
        cauchyDedekindGapRouterFromEventFlow
          (cauchyDedekindGapRouterToEventFlow y) :=
    congrArg cauchyDedekindGapRouterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyDedekindGapRouterBHistCarrier : BHistCarrier CauchyDedekindGapRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDedekindGapRouterToEventFlow
  fromEventFlow := cauchyDedekindGapRouterFromEventFlow

instance cauchyDedekindGapRouterChapterTasteGate :
    ChapterTasteGate CauchyDedekindGapRouterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyDedekindGapRouterFromEventFlow
        (cauchyDedekindGapRouterToEventFlow x) = some x
    exact CauchyDedekindGapRouterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyDedekindGapRouterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyDedekindGapRouterTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyDedekindGapRouterDecodeBHist
        (cauchyDedekindGapRouterEncodeBHist h) = h) /\
      (forall x : CauchyDedekindGapRouterUp,
        cauchyDedekindGapRouterFromEventFlow
          (cauchyDedekindGapRouterToEventFlow x) = some x) /\
        (forall x y : CauchyDedekindGapRouterUp,
          cauchyDedekindGapRouterToEventFlow x =
            cauchyDedekindGapRouterToEventFlow y -> x = y) /\
          cauchyDedekindGapRouterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyDedekindGapRouterTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact CauchyDedekindGapRouterTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyDedekindGapRouterTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyDedekindGapRouterUp
