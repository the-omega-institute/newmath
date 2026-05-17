import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StructuralAdjacencyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StructuralAdjacencyUp : Type where
  | mk (G R A H C P N : BHist) : StructuralAdjacencyUp

def structuralAdjacencyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: structuralAdjacencyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: structuralAdjacencyEncodeBHist h

def structuralAdjacencyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (structuralAdjacencyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (structuralAdjacencyDecodeBHist tail)

private theorem structuralAdjacencyDecodeEncodeBHist :
    ∀ h : BHist, structuralAdjacencyDecodeBHist (structuralAdjacencyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem structuralAdjacency_mk_congr
    {G G' R R' A A' H H' C C' P P' N N' : BHist}
    (hG : G' = G) (hR : R' = R) (hA : A' = A) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    StructuralAdjacencyUp.mk G' R' A' H' C' P' N' =
      StructuralAdjacencyUp.mk G R A H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hG
  cases hR
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def structuralAdjacencyFields : StructuralAdjacencyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StructuralAdjacencyUp.mk G R A H C P N => [G, R, A, H, C, P, N]

def structuralAdjacencyToEventFlow : StructuralAdjacencyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (structuralAdjacencyFields x).map structuralAdjacencyEncodeBHist

def structuralAdjacencyFromEventFlow : EventFlow → Option StructuralAdjacencyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _G :: [] => none
  | _G :: _R :: [] => none
  | _G :: _R :: _A :: [] => none
  | _G :: _R :: _A :: _H :: [] => none
  | _G :: _R :: _A :: _H :: _C :: [] => none
  | _G :: _R :: _A :: _H :: _C :: _P :: [] => none
  | G :: R :: A :: H :: C :: P :: N :: [] =>
      some
        (StructuralAdjacencyUp.mk
          (structuralAdjacencyDecodeBHist G)
          (structuralAdjacencyDecodeBHist R)
          (structuralAdjacencyDecodeBHist A)
          (structuralAdjacencyDecodeBHist H)
          (structuralAdjacencyDecodeBHist C)
          (structuralAdjacencyDecodeBHist P)
          (structuralAdjacencyDecodeBHist N))
  | _G :: _R :: _A :: _H :: _C :: _P :: _N :: _extra :: _rest => none

private theorem structuralAdjacency_round_trip :
    ∀ x : StructuralAdjacencyUp,
      structuralAdjacencyFromEventFlow (structuralAdjacencyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk G R A H C P N =>
      exact
        congrArg some
          (structuralAdjacency_mk_congr
            (structuralAdjacencyDecodeEncodeBHist G)
            (structuralAdjacencyDecodeEncodeBHist R)
            (structuralAdjacencyDecodeEncodeBHist A)
            (structuralAdjacencyDecodeEncodeBHist H)
            (structuralAdjacencyDecodeEncodeBHist C)
            (structuralAdjacencyDecodeEncodeBHist P)
            (structuralAdjacencyDecodeEncodeBHist N))

private theorem structuralAdjacencyToEventFlow_injective
    {x y : StructuralAdjacencyUp} :
    structuralAdjacencyToEventFlow x = structuralAdjacencyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      structuralAdjacencyFromEventFlow (structuralAdjacencyToEventFlow x) =
        structuralAdjacencyFromEventFlow (structuralAdjacencyToEventFlow y) :=
    congrArg structuralAdjacencyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (structuralAdjacency_round_trip x).symm
      (Eq.trans hread (structuralAdjacency_round_trip y)))

private theorem structuralAdjacency_fields_faithful :
    ∀ x y : StructuralAdjacencyUp,
      structuralAdjacencyFields x = structuralAdjacencyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk G₁ R₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk G₂ R₂ A₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance structuralAdjacencyBHistCarrier : BHistCarrier StructuralAdjacencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := structuralAdjacencyToEventFlow
  fromEventFlow := structuralAdjacencyFromEventFlow

instance structuralAdjacencyChapterTasteGate : ChapterTasteGate StructuralAdjacencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change structuralAdjacencyFromEventFlow (structuralAdjacencyToEventFlow x) = some x
    exact structuralAdjacency_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (structuralAdjacencyToEventFlow_injective heq)

instance structuralAdjacencyFieldFaithful : FieldFaithful StructuralAdjacencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := structuralAdjacencyFields
  field_faithful := structuralAdjacency_fields_faithful

instance structuralAdjacencyNontrivial : Nontrivial StructuralAdjacencyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StructuralAdjacencyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      StructuralAdjacencyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem StructuralAdjacencyTasteGate_single_carrier_alignment :
    (∀ h : BHist, structuralAdjacencyDecodeBHist (structuralAdjacencyEncodeBHist h) = h) ∧
      (∀ x : StructuralAdjacencyUp,
        structuralAdjacencyFromEventFlow (structuralAdjacencyToEventFlow x) = some x) ∧
        (∀ x y : StructuralAdjacencyUp,
          structuralAdjacencyToEventFlow x = structuralAdjacencyToEventFlow y → x = y) ∧
          structuralAdjacencyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨structuralAdjacencyDecodeEncodeBHist,
      structuralAdjacency_round_trip,
      (fun _ _ heq => structuralAdjacencyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.StructuralAdjacencyUp
