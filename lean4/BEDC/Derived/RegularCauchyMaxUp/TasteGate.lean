import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMaxUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMaxUp : Type where
  | mk :
      (A B WA WB DA DB S Delta V T Q R E H C P N : BHist) →
      RegularCauchyMaxUp
  deriving DecidableEq

def regularCauchyMaxEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMaxEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMaxEncodeBHist h

def regularCauchyMaxDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMaxDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMaxDecodeBHist tail)

private theorem RegularCauchyMaxTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyMaxDecodeBHist (regularCauchyMaxEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyMaxFields : RegularCauchyMaxUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMaxUp.mk A B WA WB DA DB S Delta V T Q R E H C P N =>
      [A, B, WA, WB, DA, DB, S, Delta, V, T, Q, R, E, H, C, P, N]

def regularCauchyMaxToEventFlow : RegularCauchyMaxUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyMaxFields x).map regularCauchyMaxEncodeBHist

def regularCauchyMaxFromEventFlow : EventFlow → Option RegularCauchyMaxUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: restA =>
      match restA with
      | B :: restB =>
          match restB with
          | WA :: restWA =>
              match restWA with
              | WB :: restWB =>
                  match restWB with
                  | DA :: restDA =>
                      match restDA with
                      | DB :: restDB =>
                          match restDB with
                          | S :: restS =>
                              match restS with
                              | Delta :: restDelta =>
                                  match restDelta with
                                  | V :: restV =>
                                      match restV with
                                      | T :: restT =>
                                          match restT with
                                          | Q :: restQ =>
                                              match restQ with
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
                                                                            (RegularCauchyMaxUp.mk
                                                                              (regularCauchyMaxDecodeBHist A)
                                                                              (regularCauchyMaxDecodeBHist B)
                                                                              (regularCauchyMaxDecodeBHist WA)
                                                                              (regularCauchyMaxDecodeBHist WB)
                                                                              (regularCauchyMaxDecodeBHist DA)
                                                                              (regularCauchyMaxDecodeBHist DB)
                                                                              (regularCauchyMaxDecodeBHist S)
                                                                              (regularCauchyMaxDecodeBHist Delta)
                                                                              (regularCauchyMaxDecodeBHist V)
                                                                              (regularCauchyMaxDecodeBHist T)
                                                                              (regularCauchyMaxDecodeBHist Q)
                                                                              (regularCauchyMaxDecodeBHist R)
                                                                              (regularCauchyMaxDecodeBHist E)
                                                                              (regularCauchyMaxDecodeBHist H)
                                                                              (regularCauchyMaxDecodeBHist C)
                                                                              (regularCauchyMaxDecodeBHist P)
                                                                              (regularCauchyMaxDecodeBHist N))
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
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem regularCauchyMax_mk_congr
    {A A' B B' WA WA' WB WB' DA DA' DB DB' S S' Delta Delta' V V' T T'
      Q Q' R R' E E' H H' C C' P P' N N' : BHist}
    (hA : A' = A) (hB : B' = B) (hWA : WA' = WA) (hWB : WB' = WB)
    (hDA : DA' = DA) (hDB : DB' = DB) (hS : S' = S)
    (hDelta : Delta' = Delta) (hV : V' = V) (hT : T' = T)
    (hQ : Q' = Q) (hR : R' = R) (hE : E' = E) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    RegularCauchyMaxUp.mk A' B' WA' WB' DA' DB' S' Delta' V' T' Q' R' E' H' C' P' N' =
      RegularCauchyMaxUp.mk A B WA WB DA DB S Delta V T Q R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hWA
  cases hWB
  cases hDA
  cases hDB
  cases hS
  cases hDelta
  cases hV
  cases hT
  cases hQ
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RegularCauchyMaxTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyMaxUp,
      regularCauchyMaxFromEventFlow (regularCauchyMaxToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B WA WB DA DB S Delta V T Q R E H C P N =>
      exact
        congrArg some
          (regularCauchyMax_mk_congr
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode A)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode B)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode WA)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode WB)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode DA)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode DB)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode S)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode Delta)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode V)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode T)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode Q)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode R)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode E)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode H)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode C)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode P)
            (RegularCauchyMaxTasteGate_single_carrier_alignment_decode N))

private theorem regularCauchyMaxToEventFlow_injective
    {x y : RegularCauchyMaxUp} :
    regularCauchyMaxToEventFlow x = regularCauchyMaxToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMaxFromEventFlow (regularCauchyMaxToEventFlow x) =
        regularCauchyMaxFromEventFlow (regularCauchyMaxToEventFlow y) :=
    congrArg regularCauchyMaxFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyMaxTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyMaxTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMaxBHistCarrier : BHistCarrier RegularCauchyMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMaxToEventFlow
  fromEventFlow := regularCauchyMaxFromEventFlow

instance regularCauchyMaxChapterTasteGate :
    ChapterTasteGate RegularCauchyMaxUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMaxFromEventFlow (regularCauchyMaxToEventFlow x) = some x
    exact RegularCauchyMaxTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMaxToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyMaxUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMaxChapterTasteGate

theorem RegularCauchyMaxTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyMaxDecodeBHist (regularCauchyMaxEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMaxUp,
        regularCauchyMaxFromEventFlow (regularCauchyMaxToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyMaxUp,
        regularCauchyMaxToEventFlow x = regularCauchyMaxToEventFlow y → x = y) ∧
      regularCauchyMaxEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyMaxTasteGate_single_carrier_alignment_decode
  constructor
  · exact RegularCauchyMaxTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact regularCauchyMaxToEventFlow_injective heq
  · rfl

end BEDC.Derived.RegularCauchyMaxUp
