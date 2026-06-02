import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NeighborhoodFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NeighborhoodFunctionUp : Type where
  | mk (W B A V O L H C P N : BHist) : NeighborhoodFunctionUp
  deriving DecidableEq

def neighborhoodFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: neighborhoodFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: neighborhoodFunctionEncodeBHist h

def neighborhoodFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (neighborhoodFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (neighborhoodFunctionDecodeBHist tail)

private theorem NeighborhoodFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      neighborhoodFunctionDecodeBHist (neighborhoodFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem neighborhoodFunction_mk_congr
    {W W' B B' A A' V V' O O' L L' H H' C C' P P' N N' : BHist}
    (hW : W' = W) (hB : B' = B) (hA : A' = A) (hV : V' = V)
    (hO : O' = O) (hL : L' = L) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    NeighborhoodFunctionUp.mk W' B' A' V' O' L' H' C' P' N' =
      NeighborhoodFunctionUp.mk W B A V O L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hW
  cases hB
  cases hA
  cases hV
  cases hO
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def neighborhoodFunctionToEventFlow : NeighborhoodFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NeighborhoodFunctionUp.mk W B A V O L H C P N =>
      [neighborhoodFunctionEncodeBHist W,
        neighborhoodFunctionEncodeBHist B,
        neighborhoodFunctionEncodeBHist A,
        neighborhoodFunctionEncodeBHist V,
        neighborhoodFunctionEncodeBHist O,
        neighborhoodFunctionEncodeBHist L,
        neighborhoodFunctionEncodeBHist H,
        neighborhoodFunctionEncodeBHist C,
        neighborhoodFunctionEncodeBHist P,
        neighborhoodFunctionEncodeBHist N]

def neighborhoodFunctionFromEventFlow : EventFlow → Option NeighborhoodFunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | W :: restW =>
      match restW with
      | B :: restB =>
          match restB with
          | A :: restA =>
              match restA with
              | V :: restV =>
                  match restV with
                  | O :: restO =>
                      match restO with
                      | L :: restL =>
                          match restL with
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
                                                (NeighborhoodFunctionUp.mk
                                                  (neighborhoodFunctionDecodeBHist W)
                                                  (neighborhoodFunctionDecodeBHist B)
                                                  (neighborhoodFunctionDecodeBHist A)
                                                  (neighborhoodFunctionDecodeBHist V)
                                                  (neighborhoodFunctionDecodeBHist O)
                                                  (neighborhoodFunctionDecodeBHist L)
                                                  (neighborhoodFunctionDecodeBHist H)
                                                  (neighborhoodFunctionDecodeBHist C)
                                                  (neighborhoodFunctionDecodeBHist P)
                                                  (neighborhoodFunctionDecodeBHist N))
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

private theorem NeighborhoodFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NeighborhoodFunctionUp,
      neighborhoodFunctionFromEventFlow (neighborhoodFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W B A V O L H C P N =>
      exact
        congrArg some
          (neighborhoodFunction_mk_congr
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode W)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode B)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode A)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode V)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode O)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode L)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode H)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode C)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode P)
            (NeighborhoodFunctionTasteGate_single_carrier_alignment_decode N))

private theorem NeighborhoodFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NeighborhoodFunctionUp} :
    neighborhoodFunctionToEventFlow x = neighborhoodFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      neighborhoodFunctionFromEventFlow (neighborhoodFunctionToEventFlow x) =
        neighborhoodFunctionFromEventFlow (neighborhoodFunctionToEventFlow y) :=
    congrArg neighborhoodFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (NeighborhoodFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (NeighborhoodFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance neighborhoodFunctionBHistCarrier : BHistCarrier NeighborhoodFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := neighborhoodFunctionToEventFlow
  fromEventFlow := neighborhoodFunctionFromEventFlow

instance neighborhoodFunctionChapterTasteGate :
    ChapterTasteGate NeighborhoodFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change neighborhoodFunctionFromEventFlow (neighborhoodFunctionToEventFlow x) = some x
    exact NeighborhoodFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NeighborhoodFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NeighborhoodFunctionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate NeighborhoodFunctionUp) ∧
      (∀ h : BHist, neighborhoodFunctionDecodeBHist (neighborhoodFunctionEncodeBHist h) = h) ∧
      (∀ x : NeighborhoodFunctionUp,
        neighborhoodFunctionFromEventFlow (neighborhoodFunctionToEventFlow x) = some x) ∧
      neighborhoodFunctionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact
      ⟨{
        round_trip := by
          intro x
          change neighborhoodFunctionFromEventFlow (neighborhoodFunctionToEventFlow x) = some x
          exact NeighborhoodFunctionTasteGate_single_carrier_alignment_round_trip x
        layer_separation := by
          intro x y hxy heq
          exact hxy (NeighborhoodFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)
      }⟩
  constructor
  · exact NeighborhoodFunctionTasteGate_single_carrier_alignment_decode
  constructor
  · exact NeighborhoodFunctionTasteGate_single_carrier_alignment_round_trip
  · rfl

end BEDC.Derived.NeighborhoodFunctionUp
