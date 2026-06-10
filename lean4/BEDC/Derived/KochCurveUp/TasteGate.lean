import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KochCurveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KochCurveUp : Type where
  | mk (A S D W Q E L H C P N : BHist) : KochCurveUp

def kochCurveEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kochCurveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kochCurveEncodeBHist h

def kochCurveDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kochCurveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kochCurveDecodeBHist tail)

private theorem kochCurveDecodeEncode :
    forall h : BHist, kochCurveDecodeBHist (kochCurveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kochCurveFields : KochCurveUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KochCurveUp.mk A S D W Q E L H C P N => [A, S, D, W, Q, E, L, H, C, P, N]

def kochCurveToEventFlow : KochCurveUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KochCurveUp.mk A S D W Q E L H C P N =>
      [kochCurveEncodeBHist A,
        kochCurveEncodeBHist S,
        kochCurveEncodeBHist D,
        kochCurveEncodeBHist W,
        kochCurveEncodeBHist Q,
        kochCurveEncodeBHist E,
        kochCurveEncodeBHist L,
        kochCurveEncodeBHist H,
        kochCurveEncodeBHist C,
        kochCurveEncodeBHist P,
        kochCurveEncodeBHist N]

def kochCurveFromEventFlow : EventFlow -> Option KochCurveUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: restA =>
      match restA with
      | [] => none
      | S :: restS =>
          match restS with
          | [] => none
          | D :: restD =>
              match restD with
              | [] => none
              | W :: restW =>
                  match restW with
                  | [] => none
                  | Q :: restQ =>
                      match restQ with
                      | [] => none
                      | E :: restE =>
                          match restE with
                          | [] => none
                          | L :: restL =>
                              match restL with
                              | [] => none
                              | H :: restH =>
                                  match restH with
                                  | [] => none
                                  | C :: restC =>
                                      match restC with
                                      | [] => none
                                      | P :: restP =>
                                          match restP with
                                          | [] => none
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (KochCurveUp.mk
                                                      (kochCurveDecodeBHist A)
                                                      (kochCurveDecodeBHist S)
                                                      (kochCurveDecodeBHist D)
                                                      (kochCurveDecodeBHist W)
                                                      (kochCurveDecodeBHist Q)
                                                      (kochCurveDecodeBHist E)
                                                      (kochCurveDecodeBHist L)
                                                      (kochCurveDecodeBHist H)
                                                      (kochCurveDecodeBHist C)
                                                      (kochCurveDecodeBHist P)
                                                      (kochCurveDecodeBHist N))
                                              | _ :: _ => none

private theorem kochCurve_mk_congr
    {A' S' D' W' Q' E' L' H' C' P' N' A S D W Q E L H C P N : BHist}
    (hA : A' = A) (hS : S' = S) (hD : D' = D) (hW : W' = W) (hQ : Q' = Q)
    (hE : E' = E) (hL : L' = L) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    KochCurveUp.mk A' S' D' W' Q' E' L' H' C' P' N' =
      KochCurveUp.mk A S D W Q E L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hS
  cases hD
  cases hW
  cases hQ
  cases hE
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem kochCurve_round_trip :
    forall x : KochCurveUp, kochCurveFromEventFlow (kochCurveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A S D W Q E L H C P N =>
      change
        some
          (KochCurveUp.mk
            (kochCurveDecodeBHist (kochCurveEncodeBHist A))
            (kochCurveDecodeBHist (kochCurveEncodeBHist S))
            (kochCurveDecodeBHist (kochCurveEncodeBHist D))
            (kochCurveDecodeBHist (kochCurveEncodeBHist W))
            (kochCurveDecodeBHist (kochCurveEncodeBHist Q))
            (kochCurveDecodeBHist (kochCurveEncodeBHist E))
            (kochCurveDecodeBHist (kochCurveEncodeBHist L))
            (kochCurveDecodeBHist (kochCurveEncodeBHist H))
            (kochCurveDecodeBHist (kochCurveEncodeBHist C))
            (kochCurveDecodeBHist (kochCurveEncodeBHist P))
            (kochCurveDecodeBHist (kochCurveEncodeBHist N))) =
          some (KochCurveUp.mk A S D W Q E L H C P N)
      exact
        congrArg some
          (kochCurve_mk_congr
            (kochCurveDecodeEncode A)
            (kochCurveDecodeEncode S)
            (kochCurveDecodeEncode D)
            (kochCurveDecodeEncode W)
            (kochCurveDecodeEncode Q)
            (kochCurveDecodeEncode E)
            (kochCurveDecodeEncode L)
            (kochCurveDecodeEncode H)
            (kochCurveDecodeEncode C)
            (kochCurveDecodeEncode P)
            (kochCurveDecodeEncode N))

private theorem kochCurveToEventFlow_injective {x y : KochCurveUp} :
    kochCurveToEventFlow x = kochCurveToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kochCurveFromEventFlow (kochCurveToEventFlow x) =
        kochCurveFromEventFlow (kochCurveToEventFlow y) :=
    congrArg kochCurveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kochCurve_round_trip x).symm (Eq.trans hread (kochCurve_round_trip y)))

private theorem kochCurve_field_faithful :
    forall x y : KochCurveUp, kochCurveFields x = kochCurveFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 S1 D1 W1 Q1 E1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 S2 D2 W2 Q2 E2 L2 H2 C2 P2 N2 =>
          change [A1, S1, D1, W1, Q1, E1, L1, H1, C1, P1, N1] =
            [A2, S2, D2, W2, Q2, E2, L2, H2, C2, P2, N2] at hfields
          cases hfields
          rfl

instance kochCurveBHistCarrier : BHistCarrier KochCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kochCurveToEventFlow
  fromEventFlow := kochCurveFromEventFlow

instance kochCurveChapterTasteGate : ChapterTasteGate KochCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kochCurveFromEventFlow (kochCurveToEventFlow x) = some x
    exact kochCurve_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kochCurveToEventFlow_injective heq)

instance kochCurveFieldFaithful : FieldFaithful KochCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kochCurveFields
  field_faithful := kochCurve_field_faithful

instance kochCurveNontrivial : Nontrivial KochCurveUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KochCurveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KochCurveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem KochCurveTasteGate_single_carrier_alignment :
    (∀ h : BHist, kochCurveDecodeBHist (kochCurveEncodeBHist h) = h) ∧
      (∀ x : KochCurveUp, kochCurveFromEventFlow (kochCurveToEventFlow x) = some x) ∧
        (∀ x y : KochCurveUp,
          kochCurveToEventFlow x = kochCurveToEventFlow y -> x = y) ∧
          kochCurveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact kochCurveDecodeEncode
  · constructor
    · exact kochCurve_round_trip
    · constructor
      · intro x y heq
        exact kochCurveToEventFlow_injective heq
      · rfl

end BEDC.Derived.KochCurveUp
