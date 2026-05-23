import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyQuotientBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyQuotientBoundaryUp : Type where
  | mk (S Q F D W R E H C P N : BHist) : CauchyQuotientBoundaryUp
  deriving DecidableEq

def cauchyQuotientBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyQuotientBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyQuotientBoundaryEncodeBHist h

def cauchyQuotientBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyQuotientBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyQuotientBoundaryDecodeBHist tail)

private theorem CauchyQuotientBoundaryUp_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyQuotientBoundaryFields : CauchyQuotientBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyQuotientBoundaryUp.mk S Q F D W R E H C P N => [S, Q, F, D, W, R, E, H, C, P, N]

def cauchyQuotientBoundaryToEventFlow : CauchyQuotientBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyQuotientBoundaryFields x).map cauchyQuotientBoundaryEncodeBHist

def cauchyQuotientBoundaryFromEventFlow : EventFlow → Option CauchyQuotientBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | Q :: restQ =>
          match restQ with
          | F :: restF =>
              match restF with
              | D :: restD =>
                  match restD with
                  | W :: restW =>
                      match restW with
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
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (CauchyQuotientBoundaryUp.mk
                                                      (cauchyQuotientBoundaryDecodeBHist S)
                                                      (cauchyQuotientBoundaryDecodeBHist Q)
                                                      (cauchyQuotientBoundaryDecodeBHist F)
                                                      (cauchyQuotientBoundaryDecodeBHist D)
                                                      (cauchyQuotientBoundaryDecodeBHist W)
                                                      (cauchyQuotientBoundaryDecodeBHist R)
                                                      (cauchyQuotientBoundaryDecodeBHist E)
                                                      (cauchyQuotientBoundaryDecodeBHist H)
                                                      (cauchyQuotientBoundaryDecodeBHist C)
                                                      (cauchyQuotientBoundaryDecodeBHist P)
                                                      (cauchyQuotientBoundaryDecodeBHist N))
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

private theorem cauchyQuotientBoundary_mk_congr
    {S S' Q Q' F F' D D' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hQ : Q' = Q) (hF : F' = F) (hD : D' = D)
    (hW : W' = W) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyQuotientBoundaryUp.mk S' Q' F' D' W' R' E' H' C' P' N' =
      CauchyQuotientBoundaryUp.mk S Q F D W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hQ
  cases hF
  cases hD
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyQuotientBoundaryUp_single_carrier_alignment_round_trip :
    ∀ x : CauchyQuotientBoundaryUp,
      cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q F D W R E H C P N =>
      exact congrArg some
        (cauchyQuotientBoundary_mk_congr
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode S)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode Q)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode F)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode D)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode W)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode R)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode E)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode H)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode C)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode P)
          (CauchyQuotientBoundaryUp_single_carrier_alignment_decode N))

private theorem cauchyQuotientBoundaryToEventFlow_injective
    {x y : CauchyQuotientBoundaryUp} :
    cauchyQuotientBoundaryToEventFlow x = cauchyQuotientBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) =
        cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow y) :=
    congrArg cauchyQuotientBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyQuotientBoundaryUp_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyQuotientBoundaryUp_single_carrier_alignment_round_trip y)))

instance cauchyQuotientBoundaryBHistCarrier :
    BHistCarrier CauchyQuotientBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyQuotientBoundaryToEventFlow
  fromEventFlow := cauchyQuotientBoundaryFromEventFlow

instance cauchyQuotientBoundaryChapterTasteGate :
    ChapterTasteGate CauchyQuotientBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) =
      some x
    exact CauchyQuotientBoundaryUp_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyQuotientBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyQuotientBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyQuotientBoundaryChapterTasteGate

theorem CauchyQuotientBoundaryUp_single_carrier_alignment :
    (∀ h : BHist,
      cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist h) = h) ∧
      (∀ x : CauchyQuotientBoundaryUp,
        cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyQuotientBoundaryUp,
        cauchyQuotientBoundaryToEventFlow x = cauchyQuotientBoundaryToEventFlow y →
          x = y) ∧
      cauchyQuotientBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyQuotientBoundaryUp_single_carrier_alignment_decode
  constructor
  · exact CauchyQuotientBoundaryUp_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyQuotientBoundaryToEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyQuotientBoundaryUp

namespace BEDC.Derived.CauchyQuotientBoundaryUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.Derived.CauchyQuotientBoundaryUp

theorem CauchyQuotientBoundaryUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyQuotientBoundaryDecodeBHist (cauchyQuotientBoundaryEncodeBHist h) = h) ∧
      (∀ x : CauchyQuotientBoundaryUp,
        cauchyQuotientBoundaryFromEventFlow (cauchyQuotientBoundaryToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyQuotientBoundaryUp,
        cauchyQuotientBoundaryToEventFlow x = cauchyQuotientBoundaryToEventFlow y →
          x = y) ∧
      cauchyQuotientBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact BEDC.Derived.CauchyQuotientBoundaryUp.CauchyQuotientBoundaryUp_single_carrier_alignment

end BEDC.Derived.CauchyQuotientBoundaryUp.TasteGate
