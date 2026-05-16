import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedPhysicalInductionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedPhysicalInductionUp : Type where
  | mk : (H U T S O A C B F L K P N : BHist) → RealityConstrainedPhysicalInductionUp
  deriving DecidableEq

def realityConstrainedPhysicalInductionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedPhysicalInductionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedPhysicalInductionEncodeBHist h

def realityConstrainedPhysicalInductionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedPhysicalInductionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedPhysicalInductionDecodeBHist tail)

private theorem RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realityConstrainedPhysicalInductionDecodeBHist
        (realityConstrainedPhysicalInductionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_mk_congr
    {H H' U U' T T' S S' O O' A A' C C' B B' F F' L L' K K' P P' N N' :
      BHist}
    (hH : H' = H) (hU : U' = U) (hT : T' = T) (hS : S' = S) (hO : O' = O)
    (hA : A' = A) (hC : C' = C) (hB : B' = B) (hF : F' = F) (hL : L' = L)
    (hK : K' = K) (hP : P' = P) (hN : N' = N) :
    RealityConstrainedPhysicalInductionUp.mk H' U' T' S' O' A' C' B' F' L' K' P' N' =
      RealityConstrainedPhysicalInductionUp.mk H U T S O A C B F L K P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hH
  cases hU
  cases hT
  cases hS
  cases hO
  cases hA
  cases hC
  cases hB
  cases hF
  cases hL
  cases hK
  cases hP
  cases hN
  rfl

def realityConstrainedPhysicalInductionFields :
    RealityConstrainedPhysicalInductionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedPhysicalInductionUp.mk H U T S O A C B F L K P N =>
      [H, U, T, S, O, A, C, B, F, L, K, P, N]

def realityConstrainedPhysicalInductionToEventFlow :
    RealityConstrainedPhysicalInductionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (realityConstrainedPhysicalInductionFields x).map
        realityConstrainedPhysicalInductionEncodeBHist

private def RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
        index rest

def realityConstrainedPhysicalInductionFromEventFlow :
    EventFlow → Option RealityConstrainedPhysicalInductionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealityConstrainedPhysicalInductionUp.mk
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              0 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              1 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              2 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              3 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              4 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              5 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              6 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              7 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              8 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              9 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              10 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              11 ef))
          (realityConstrainedPhysicalInductionDecodeBHist
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_eventAtDefault
              12 ef)))

private theorem RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealityConstrainedPhysicalInductionUp,
      realityConstrainedPhysicalInductionFromEventFlow
        (realityConstrainedPhysicalInductionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H U T S O A C B F L K P N =>
      exact
        congrArg some
          (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_mk_congr
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode H)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode U)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode T)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode S)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode O)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode A)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode C)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode B)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode F)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode L)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode K)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode P)
            (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode N))

private theorem RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_injective
    {x y : RealityConstrainedPhysicalInductionUp} :
    realityConstrainedPhysicalInductionToEventFlow x =
      realityConstrainedPhysicalInductionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedPhysicalInductionFromEventFlow
          (realityConstrainedPhysicalInductionToEventFlow x) =
        realityConstrainedPhysicalInductionFromEventFlow
          (realityConstrainedPhysicalInductionToEventFlow y) :=
    congrArg realityConstrainedPhysicalInductionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealityConstrainedPhysicalInductionUp,
      realityConstrainedPhysicalInductionFields x =
        realityConstrainedPhysicalInductionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ U₁ T₁ S₁ O₁ A₁ C₁ B₁ F₁ L₁ K₁ P₁ N₁ =>
      cases y with
      | mk H₂ U₂ T₂ S₂ O₂ A₂ C₂ B₂ F₂ L₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance realityConstrainedPhysicalInductionBHistCarrier :
    BHistCarrier RealityConstrainedPhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedPhysicalInductionToEventFlow
  fromEventFlow := realityConstrainedPhysicalInductionFromEventFlow

instance realityConstrainedPhysicalInductionChapterTasteGate :
    ChapterTasteGate RealityConstrainedPhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedPhysicalInductionFromEventFlow
        (realityConstrainedPhysicalInductionToEventFlow x) = some x
    exact RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_injective heq)

instance realityConstrainedPhysicalInductionFieldFaithful :
    FieldFaithful RealityConstrainedPhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedPhysicalInductionFields
  field_faithful := RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_fields

instance realityConstrainedPhysicalInductionNontrivial :
    Nontrivial RealityConstrainedPhysicalInductionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedPhysicalInductionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedPhysicalInductionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedPhysicalInductionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedPhysicalInductionChapterTasteGate

theorem RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedPhysicalInductionDecodeBHist
        (realityConstrainedPhysicalInductionEncodeBHist h) = h) ∧
      realityConstrainedPhysicalInductionEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ x : RealityConstrainedPhysicalInductionUp,
          realityConstrainedPhysicalInductionFromEventFlow
            (realityConstrainedPhysicalInductionToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_decode, rfl,
      RealityConstrainedPhysicalInductionTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.RealityConstrainedPhysicalInductionUp
