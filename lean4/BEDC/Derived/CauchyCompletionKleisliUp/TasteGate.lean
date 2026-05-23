import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionKleisliUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionKleisliUp : Type where
  | mk (U B A S W D R E H C P N : BHist) : CauchyCompletionKleisliUp
  deriving DecidableEq

def cauchyCompletionKleisliEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionKleisliEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionKleisliEncodeBHist h

def cauchyCompletionKleisliDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionKleisliDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionKleisliDecodeBHist tail)

private theorem CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionKleisliDecodeBHist (cauchyCompletionKleisliEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionKleisliFields : CauchyCompletionKleisliUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionKleisliUp.mk U B A S W D R E H C P N =>
      [U, B, A, S, W, D, R, E, H, C, P, N]

def cauchyCompletionKleisliToEventFlow : CauchyCompletionKleisliUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionKleisliFields x).map cauchyCompletionKleisliEncodeBHist

def cauchyCompletionKleisliFromEventFlow : EventFlow → Option CauchyCompletionKleisliUp
  -- BEDC touchpoint anchor: BHist BMark
  | U :: restU =>
      match restU with
      | B :: restB =>
          match restB with
          | A :: restA =>
              match restA with
              | S :: restS =>
                  match restS with
                  | W :: restW =>
                      match restW with
                      | D :: restD =>
                          match restD with
                          | R :: restR =>
                              match restR with
                              | E :: restE =>
                                  match restE with
                                  | H :: restH =>
                                      match restH with
                                      | C :: restC =>
                                          match restC with
                                          | P :: restP =>
                                              match restP with
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (CauchyCompletionKleisliUp.mk
                                                          (cauchyCompletionKleisliDecodeBHist U)
                                                          (cauchyCompletionKleisliDecodeBHist B)
                                                          (cauchyCompletionKleisliDecodeBHist A)
                                                          (cauchyCompletionKleisliDecodeBHist S)
                                                          (cauchyCompletionKleisliDecodeBHist W)
                                                          (cauchyCompletionKleisliDecodeBHist D)
                                                          (cauchyCompletionKleisliDecodeBHist R)
                                                          (cauchyCompletionKleisliDecodeBHist E)
                                                          (cauchyCompletionKleisliDecodeBHist H)
                                                          (cauchyCompletionKleisliDecodeBHist C)
                                                          (cauchyCompletionKleisliDecodeBHist P)
                                                          (cauchyCompletionKleisliDecodeBHist N))
                                                  | _ :: _ => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyCompletionKleisli_mk_congr
    {U U' B B' A A' S S' W W' D D' R R' E E' H H' C C' P P' N N' : BHist}
    (hU : U' = U) (hB : B' = B) (hA : A' = A) (hS : S' = S)
    (hW : W' = W) (hD : D' = D) (hR : R' = R) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyCompletionKleisliUp.mk U' B' A' S' W' D' R' E' H' C' P' N' =
      CauchyCompletionKleisliUp.mk U B A S W D R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hU
  cases hB
  cases hA
  cases hS
  cases hW
  cases hD
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionKleisliUp,
      cauchyCompletionKleisliFromEventFlow (cauchyCompletionKleisliToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U B A S W D R E H C P N =>
      exact
        congrArg some
          (cauchyCompletionKleisli_mk_congr
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode U)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode B)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode A)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode S)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode W)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode D)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode R)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode E)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode H)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode C)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode P)
            (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode N))

private theorem cauchyCompletionKleisliToEventFlow_injective
    {x y : CauchyCompletionKleisliUp} :
    cauchyCompletionKleisliToEventFlow x = cauchyCompletionKleisliToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionKleisliFromEventFlow (cauchyCompletionKleisliToEventFlow x) =
        cauchyCompletionKleisliFromEventFlow (cauchyCompletionKleisliToEventFlow y) :=
    congrArg cauchyCompletionKleisliFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionKleisliBHistCarrier : BHistCarrier CauchyCompletionKleisliUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionKleisliToEventFlow
  fromEventFlow := cauchyCompletionKleisliFromEventFlow

instance cauchyCompletionKleisliChapterTasteGate :
    ChapterTasteGate CauchyCompletionKleisliUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionKleisliFromEventFlow (cauchyCompletionKleisliToEventFlow x) =
        some x
    exact CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionKleisliToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionKleisliUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionKleisliChapterTasteGate

theorem CauchyCompletionKleisliUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionKleisliDecodeBHist (cauchyCompletionKleisliEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionKleisliUp,
        cauchyCompletionKleisliFromEventFlow (cauchyCompletionKleisliToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCompletionKleisliUp,
        cauchyCompletionKleisliToEventFlow x = cauchyCompletionKleisliToEventFlow y →
          x = y) ∧
      cauchyCompletionKleisliEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyCompletionKleisliUpTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyCompletionKleisliToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.CauchyCompletionKleisliUp
