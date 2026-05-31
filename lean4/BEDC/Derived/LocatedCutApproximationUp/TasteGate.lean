import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCutApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCutApproximationUp : Type where
  | mk (L U W A S R D E H C P N : BHist) : LocatedCutApproximationUp
  deriving DecidableEq

def locatedCutApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCutApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCutApproximationEncodeBHist h

def locatedCutApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCutApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCutApproximationDecodeBHist tail)

private theorem LocatedCutApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCutApproximationDecodeBHist
        (locatedCutApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCutApproximationFields : LocatedCutApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCutApproximationUp.mk L U W A S R D E H C P N =>
      [L, U, W, A, S, R, D, E, H, C, P, N]

def locatedCutApproximationToEventFlow : LocatedCutApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCutApproximationFields x).map locatedCutApproximationEncodeBHist

def locatedCutApproximationFromEventFlow : EventFlow → Option LocatedCutApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | L :: restL =>
      match restL with
      | U :: restU =>
          match restU with
          | W :: restW =>
              match restW with
              | A :: restA =>
                  match restA with
                  | S :: restS =>
                      match restS with
                      | R :: restR =>
                          match restR with
                          | D :: restD =>
                              match restD with
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
                                                        (LocatedCutApproximationUp.mk
                                                          (locatedCutApproximationDecodeBHist L)
                                                          (locatedCutApproximationDecodeBHist U)
                                                          (locatedCutApproximationDecodeBHist W)
                                                          (locatedCutApproximationDecodeBHist A)
                                                          (locatedCutApproximationDecodeBHist S)
                                                          (locatedCutApproximationDecodeBHist R)
                                                          (locatedCutApproximationDecodeBHist D)
                                                          (locatedCutApproximationDecodeBHist E)
                                                          (locatedCutApproximationDecodeBHist H)
                                                          (locatedCutApproximationDecodeBHist C)
                                                          (locatedCutApproximationDecodeBHist P)
                                                          (locatedCutApproximationDecodeBHist N))
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

private theorem locatedCutApproximation_mk_congr
    {L L' U U' W W' A A' S S' R R' D D' E E' H H' C C' P P' N N' : BHist}
    (hL : L' = L) (hU : U' = U) (hW : W' = W) (hA : A' = A)
    (hS : S' = S) (hR : R' = R) (hD : D' = D) (hE : E' = E)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    LocatedCutApproximationUp.mk L' U' W' A' S' R' D' E' H' C' P' N' =
      LocatedCutApproximationUp.mk L U W A S R D E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hL
  cases hU
  cases hW
  cases hA
  cases hS
  cases hR
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem LocatedCutApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCutApproximationUp,
      locatedCutApproximationFromEventFlow
        (locatedCutApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U W A S R D E H C P N =>
      exact
        congrArg some
          (locatedCutApproximation_mk_congr
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode L)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode U)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode W)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode A)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode S)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode R)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode D)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode E)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode H)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode C)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode P)
            (LocatedCutApproximationTasteGate_single_carrier_alignment_decode N))

private theorem locatedCutApproximationToEventFlow_injective
    {x y : LocatedCutApproximationUp} :
    locatedCutApproximationToEventFlow x =
      locatedCutApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCutApproximationFromEventFlow (locatedCutApproximationToEventFlow x) =
        locatedCutApproximationFromEventFlow (locatedCutApproximationToEventFlow y) :=
    congrArg locatedCutApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCutApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCutApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCutApproximationBHistCarrier :
    BHistCarrier LocatedCutApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCutApproximationToEventFlow
  fromEventFlow := locatedCutApproximationFromEventFlow

instance locatedCutApproximationChapterTasteGate :
    ChapterTasteGate LocatedCutApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedCutApproximationFromEventFlow
        (locatedCutApproximationToEventFlow x) = some x
    exact LocatedCutApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCutApproximationToEventFlow_injective heq)

theorem LocatedCutApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCutApproximationDecodeBHist (locatedCutApproximationEncodeBHist h) = h) ∧
      (∀ x : LocatedCutApproximationUp,
        locatedCutApproximationFromEventFlow
          (locatedCutApproximationToEventFlow x) = some x) ∧
        (∀ x y : LocatedCutApproximationUp,
          locatedCutApproximationToEventFlow x = locatedCutApproximationToEventFlow y →
            x = y) ∧
          locatedCutApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedCutApproximationTasteGate_single_carrier_alignment_decode
  constructor
  · exact LocatedCutApproximationTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact locatedCutApproximationToEventFlow_injective heq
  · rfl

end BEDC.Derived.LocatedCutApproximationUp
