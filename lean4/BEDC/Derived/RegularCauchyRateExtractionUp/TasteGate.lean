import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRateExtractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRateExtractionUp : Type where
  | mk (S D R M U E H C P N : BHist) : RegularCauchyRateExtractionUp
  deriving DecidableEq

def regularCauchyRateExtractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRateExtractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRateExtractionEncodeBHist h

def regularCauchyRateExtractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRateExtractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRateExtractionDecodeBHist tail)

private theorem RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyRateExtractionDecodeBHist
        (regularCauchyRateExtractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyRateExtractionFields :
    RegularCauchyRateExtractionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRateExtractionUp.mk S D R M U E H C P N =>
      [S, D, R, M, U, E, H, C, P, N]

def regularCauchyRateExtractionToEventFlow :
    RegularCauchyRateExtractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyRateExtractionFields x).map
        regularCauchyRateExtractionEncodeBHist

def regularCauchyRateExtractionFromEventFlow :
    EventFlow → Option RegularCauchyRateExtractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | D :: restD =>
          match restD with
          | R :: restR =>
              match restR with
              | M :: restM =>
                  match restM with
                  | U :: restU =>
                      match restU with
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
                                                (RegularCauchyRateExtractionUp.mk
                                                  (regularCauchyRateExtractionDecodeBHist S)
                                                  (regularCauchyRateExtractionDecodeBHist D)
                                                  (regularCauchyRateExtractionDecodeBHist R)
                                                  (regularCauchyRateExtractionDecodeBHist M)
                                                  (regularCauchyRateExtractionDecodeBHist U)
                                                  (regularCauchyRateExtractionDecodeBHist E)
                                                  (regularCauchyRateExtractionDecodeBHist H)
                                                  (regularCauchyRateExtractionDecodeBHist C)
                                                  (regularCauchyRateExtractionDecodeBHist P)
                                                  (regularCauchyRateExtractionDecodeBHist N))
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

private theorem regularCauchyRateExtraction_mk_congr
    {S S' D D' R R' M M' U U' E E' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hD : D' = D) (hR : R' = R) (hM : M' = M)
    (hU : U' = U) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    RegularCauchyRateExtractionUp.mk S' D' R' M' U' E' H' C' P' N' =
      RegularCauchyRateExtractionUp.mk S D R M U E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hD
  cases hR
  cases hM
  cases hU
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem RegularCauchyRateExtractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyRateExtractionUp,
      regularCauchyRateExtractionFromEventFlow
        (regularCauchyRateExtractionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D R M U E H C P N =>
      exact
        congrArg some
          (regularCauchyRateExtraction_mk_congr
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode S)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode D)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode R)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode M)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode U)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode E)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode H)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode C)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode P)
            (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode N))

private theorem RegularCauchyRateExtractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyRateExtractionUp} :
    regularCauchyRateExtractionToEventFlow x =
      regularCauchyRateExtractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyRateExtractionFromEventFlow
          (regularCauchyRateExtractionToEventFlow x) =
        regularCauchyRateExtractionFromEventFlow
          (regularCauchyRateExtractionToEventFlow y) :=
    congrArg regularCauchyRateExtractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyRateExtractionBHistCarrier :
    BHistCarrier RegularCauchyRateExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRateExtractionToEventFlow
  fromEventFlow := regularCauchyRateExtractionFromEventFlow

instance regularCauchyRateExtractionChapterTasteGate :
    ChapterTasteGate RegularCauchyRateExtractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyRateExtractionFromEventFlow
        (regularCauchyRateExtractionToEventFlow x) = some x
    exact RegularCauchyRateExtractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyRateExtractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyRateExtractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyRateExtractionChapterTasteGate

theorem RegularCauchyRateExtractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyRateExtractionDecodeBHist
        (regularCauchyRateExtractionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyRateExtractionUp,
        regularCauchyRateExtractionFromEventFlow
          (regularCauchyRateExtractionToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyRateExtractionUp,
          regularCauchyRateExtractionToEventFlow x =
            regularCauchyRateExtractionToEventFlow y → x = y) ∧
          regularCauchyRateExtractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyRateExtractionTasteGate_single_carrier_alignment_decode,
      RegularCauchyRateExtractionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyRateExtractionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyRateExtractionUp
