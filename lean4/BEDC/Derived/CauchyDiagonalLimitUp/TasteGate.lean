import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDiagonalLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDiagonalLimitUp : Type where
  | mk (R B D V E S Q Y T H C P N : BHist) : CauchyDiagonalLimitUp
  deriving DecidableEq

def cauchyDiagonalLimitEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDiagonalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDiagonalLimitEncodeBHist h

def cauchyDiagonalLimitDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDiagonalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDiagonalLimitDecodeBHist tail)

private theorem CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode :
    forall h : BHist, cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyDiagonalLimitFields : CauchyDiagonalLimitUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDiagonalLimitUp.mk R B D V E S Q Y T H C P N =>
      [R, B, D, V, E, S, Q, Y, T, H, C, P, N]

def cauchyDiagonalLimitToEventFlow : CauchyDiagonalLimitUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyDiagonalLimitFields x).map cauchyDiagonalLimitEncodeBHist

def cauchyDiagonalLimitFromEventFlow : EventFlow -> Option CauchyDiagonalLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | R :: restR =>
      match restR with
      | B :: restB =>
          match restB with
          | D :: restD =>
              match restD with
              | V :: restV =>
                  match restV with
                  | E :: restE =>
                      match restE with
                      | S :: restS =>
                          match restS with
                          | Q :: restQ =>
                              match restQ with
                              | Y :: restY =>
                                  match restY with
                                  | T :: restT =>
                                      match restT with
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
                                                            (CauchyDiagonalLimitUp.mk
                                                              (cauchyDiagonalLimitDecodeBHist R)
                                                              (cauchyDiagonalLimitDecodeBHist B)
                                                              (cauchyDiagonalLimitDecodeBHist D)
                                                              (cauchyDiagonalLimitDecodeBHist V)
                                                              (cauchyDiagonalLimitDecodeBHist E)
                                                              (cauchyDiagonalLimitDecodeBHist S)
                                                              (cauchyDiagonalLimitDecodeBHist Q)
                                                              (cauchyDiagonalLimitDecodeBHist Y)
                                                              (cauchyDiagonalLimitDecodeBHist T)
                                                              (cauchyDiagonalLimitDecodeBHist H)
                                                              (cauchyDiagonalLimitDecodeBHist C)
                                                              (cauchyDiagonalLimitDecodeBHist P)
                                                              (cauchyDiagonalLimitDecodeBHist N))
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
  | [] => none

private theorem CauchyDiagonalLimitTasteGate_single_carrier_alignment_mk_congr
    {R R' B B' D D' V V' E E' S S' Q Q' Y Y' T T' H H' C C' P P' N N' : BHist}
    (hR : R' = R) (hB : B' = B) (hD : D' = D) (hV : V' = V)
    (hE : E' = E) (hS : S' = S) (hQ : Q' = Q) (hY : Y' = Y)
    (hT : T' = T) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    CauchyDiagonalLimitUp.mk R' B' D' V' E' S' Q' Y' T' H' C' P' N' =
      CauchyDiagonalLimitUp.mk R B D V E S Q Y T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hR
  cases hB
  cases hD
  cases hV
  cases hE
  cases hS
  cases hQ
  cases hY
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyDiagonalLimitTasteGate_single_carrier_alignment_round_trip :
    forall x : CauchyDiagonalLimitUp,
      cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R B D V E S Q Y T H C P N =>
      exact
        congrArg some
          (CauchyDiagonalLimitTasteGate_single_carrier_alignment_mk_congr
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode R)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode B)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode D)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode V)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode E)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode S)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode Q)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode Y)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode T)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode H)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode C)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode P)
            (CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode N))

private theorem CauchyDiagonalLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyDiagonalLimitUp} :
    cauchyDiagonalLimitToEventFlow x = cauchyDiagonalLimitToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) =
        cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow y) :=
    congrArg cauchyDiagonalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyDiagonalLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyDiagonalLimitTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyDiagonalLimitBHistCarrier : BHistCarrier CauchyDiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDiagonalLimitToEventFlow
  fromEventFlow := cauchyDiagonalLimitFromEventFlow

instance cauchyDiagonalLimitChapterTasteGate : ChapterTasteGate CauchyDiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) = some x
    exact CauchyDiagonalLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyDiagonalLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyDiagonalLimitTasteGate_single_carrier_alignment :
    (forall h : BHist, cauchyDiagonalLimitDecodeBHist (cauchyDiagonalLimitEncodeBHist h) = h) ∧
      (forall x : CauchyDiagonalLimitUp,
        cauchyDiagonalLimitFromEventFlow (cauchyDiagonalLimitToEventFlow x) = some x) ∧
        (forall x y : CauchyDiagonalLimitUp,
          cauchyDiagonalLimitToEventFlow x = cauchyDiagonalLimitToEventFlow y -> x = y) ∧
          cauchyDiagonalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyDiagonalLimitTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CauchyDiagonalLimitTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyDiagonalLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.CauchyDiagonalLimitUp
