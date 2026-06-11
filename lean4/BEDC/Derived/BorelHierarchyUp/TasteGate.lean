import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BorelHierarchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BorelHierarchyUp : Type where
  | mk (X B G P S R T C N : BHist) : BorelHierarchyUp

def borelHierarchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: borelHierarchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: borelHierarchyEncodeBHist h

def borelHierarchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (borelHierarchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (borelHierarchyDecodeBHist tail)

private theorem BorelHierarchyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, borelHierarchyDecodeBHist (borelHierarchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem borelHierarchy_mk_congr
    {X X' B B' G G' P P' S S' R R' T T' C C' N N' : BHist}
    (hX : X' = X) (hB : B' = B) (hG : G' = G) (hP : P' = P)
    (hS : S' = S) (hR : R' = R) (hT : T' = T) (hC : C' = C)
    (hN : N' = N) :
    BorelHierarchyUp.mk X' B' G' P' S' R' T' C' N' =
      BorelHierarchyUp.mk X B G P S R T C N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hX
  cases hB
  cases hG
  cases hP
  cases hS
  cases hR
  cases hT
  cases hC
  cases hN
  rfl

def borelHierarchyFields : BorelHierarchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BorelHierarchyUp.mk X B G P S R T C N => [X, B, G, P, S, R, T, C, N]

def borelHierarchyToEventFlow : BorelHierarchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map borelHierarchyEncodeBHist (borelHierarchyFields x)

def borelHierarchyFromEventFlow : EventFlow → Option BorelHierarchyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _X :: [] => none
  | _X :: _B :: [] => none
  | _X :: _B :: _G :: [] => none
  | _X :: _B :: _G :: _P :: [] => none
  | _X :: _B :: _G :: _P :: _S :: [] => none
  | _X :: _B :: _G :: _P :: _S :: _R :: [] => none
  | _X :: _B :: _G :: _P :: _S :: _R :: _T :: [] => none
  | _X :: _B :: _G :: _P :: _S :: _R :: _T :: _C :: [] => none
  | X :: B :: G :: P :: S :: R :: T :: C :: N :: [] =>
      some
        (BorelHierarchyUp.mk
          (borelHierarchyDecodeBHist X)
          (borelHierarchyDecodeBHist B)
          (borelHierarchyDecodeBHist G)
          (borelHierarchyDecodeBHist P)
          (borelHierarchyDecodeBHist S)
          (borelHierarchyDecodeBHist R)
          (borelHierarchyDecodeBHist T)
          (borelHierarchyDecodeBHist C)
          (borelHierarchyDecodeBHist N))
  | _X :: _B :: _G :: _P :: _S :: _R :: _T :: _C :: _N :: _extra :: _rest => none

private theorem BorelHierarchyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BorelHierarchyUp,
      borelHierarchyFromEventFlow (borelHierarchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B G P S R T C N =>
      exact
        congrArg some
          (borelHierarchy_mk_congr
            (BorelHierarchyTasteGate_single_carrier_alignment_decode X)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode B)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode G)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode P)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode S)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode R)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode T)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode C)
            (BorelHierarchyTasteGate_single_carrier_alignment_decode N))

private theorem BorelHierarchyTasteGate_single_carrier_alignment_injective
    {x y : BorelHierarchyUp} :
    borelHierarchyToEventFlow x = borelHierarchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      borelHierarchyFromEventFlow (borelHierarchyToEventFlow x) =
        borelHierarchyFromEventFlow (borelHierarchyToEventFlow y) :=
    congrArg borelHierarchyFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans
      (BorelHierarchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BorelHierarchyTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance borelHierarchyBHistCarrier : BHistCarrier BorelHierarchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := borelHierarchyToEventFlow
  fromEventFlow := borelHierarchyFromEventFlow

instance borelHierarchyChapterTasteGate : ChapterTasteGate BorelHierarchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change borelHierarchyFromEventFlow (borelHierarchyToEventFlow x) = some x
    exact BorelHierarchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BorelHierarchyTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate BorelHierarchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  borelHierarchyChapterTasteGate

theorem BorelHierarchyTasteGate_single_carrier_alignment :
    (∀ h : BHist, borelHierarchyDecodeBHist (borelHierarchyEncodeBHist h) = h) ∧
      (∀ x : BorelHierarchyUp,
        borelHierarchyFromEventFlow (borelHierarchyToEventFlow x) = some x) ∧
        (∀ x y : BorelHierarchyUp,
          borelHierarchyToEventFlow x = borelHierarchyToEventFlow y -> x = y) ∧
          borelHierarchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BorelHierarchyTasteGate_single_carrier_alignment_decode,
      BorelHierarchyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BorelHierarchyTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BorelHierarchyUp
