import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionAdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionAdjunctionUp : Type where
  | mk (X C D E U H P N : BHist) : CauchyCompletionAdjunctionUp
  deriving DecidableEq

def cauchyCompletionAdjunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionAdjunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionAdjunctionEncodeBHist h

def cauchyCompletionAdjunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionAdjunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionAdjunctionDecodeBHist tail)

private theorem CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionAdjunctionDecodeBHist
          (cauchyCompletionAdjunctionEncodeBHist h) =
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

def cauchyCompletionAdjunctionFields :
    CauchyCompletionAdjunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionAdjunctionUp.mk X C D E U H P N => [X, C, D, E, U, H, P, N]

def cauchyCompletionAdjunctionToEventFlow :
    CauchyCompletionAdjunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionAdjunctionFields x).map cauchyCompletionAdjunctionEncodeBHist

def cauchyCompletionAdjunctionFromEventFlow :
    EventFlow → Option CauchyCompletionAdjunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: restX =>
      match restX with
      | C :: restC =>
          match restC with
          | D :: restD =>
              match restD with
              | E :: restE =>
                  match restE with
                  | U :: restU =>
                      match restU with
                      | H :: restH =>
                          match restH with
                          | P :: restP =>
                              match restP with
                              | N :: restN =>
                                  match restN with
                                  | [] =>
                                      some
                                        (CauchyCompletionAdjunctionUp.mk
                                          (cauchyCompletionAdjunctionDecodeBHist X)
                                          (cauchyCompletionAdjunctionDecodeBHist C)
                                          (cauchyCompletionAdjunctionDecodeBHist D)
                                          (cauchyCompletionAdjunctionDecodeBHist E)
                                          (cauchyCompletionAdjunctionDecodeBHist U)
                                          (cauchyCompletionAdjunctionDecodeBHist H)
                                          (cauchyCompletionAdjunctionDecodeBHist P)
                                          (cauchyCompletionAdjunctionDecodeBHist N))
                                  | _ :: _ => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem cauchyCompletionAdjunction_mk_congr
    {X X' C C' D D' E E' U U' H H' P P' N N' : BHist}
    (hX : X' = X) (hC : C' = C) (hD : D' = D) (hE : E' = E)
    (hU : U' = U) (hH : H' = H) (hP : P' = P) (hN : N' = N) :
    CauchyCompletionAdjunctionUp.mk X' C' D' E' U' H' P' N' =
      CauchyCompletionAdjunctionUp.mk X C D E U H P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hC
  cases hD
  cases hE
  cases hU
  cases hH
  cases hP
  cases hN
  rfl

private theorem CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionAdjunctionUp,
      cauchyCompletionAdjunctionFromEventFlow
          (cauchyCompletionAdjunctionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X C D E U H P N =>
      exact
        congrArg some
          (cauchyCompletionAdjunction_mk_congr
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode X)
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode C)
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode D)
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode E)
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode U)
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode H)
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode P)
            (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode N))

private theorem cauchyCompletionAdjunctionToEventFlow_injective
    {x y : CauchyCompletionAdjunctionUp} :
    cauchyCompletionAdjunctionToEventFlow x =
        cauchyCompletionAdjunctionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionAdjunctionFromEventFlow
          (cauchyCompletionAdjunctionToEventFlow x) =
        cauchyCompletionAdjunctionFromEventFlow
          (cauchyCompletionAdjunctionToEventFlow y) :=
    congrArg cauchyCompletionAdjunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionAdjunctionBHistCarrier :
    BHistCarrier CauchyCompletionAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionAdjunctionToEventFlow
  fromEventFlow := cauchyCompletionAdjunctionFromEventFlow

instance cauchyCompletionAdjunctionChapterTasteGate :
    ChapterTasteGate CauchyCompletionAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionAdjunctionFromEventFlow
          (cauchyCompletionAdjunctionToEventFlow x) =
        some x
    exact CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionAdjunctionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyCompletionAdjunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionAdjunctionChapterTasteGate

theorem CauchyCompletionAdjunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionAdjunctionDecodeBHist
          (cauchyCompletionAdjunctionEncodeBHist h) =
        h) ∧
      (∀ x : CauchyCompletionAdjunctionUp,
        cauchyCompletionAdjunctionFromEventFlow
            (cauchyCompletionAdjunctionToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyCompletionAdjunctionUp,
        cauchyCompletionAdjunctionToEventFlow x =
            cauchyCompletionAdjunctionToEventFlow y →
          x = y) ∧
      cauchyCompletionAdjunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyCompletionAdjunctionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyCompletionAdjunctionToEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyCompletionAdjunctionUp
