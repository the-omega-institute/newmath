import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuousExtensionUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContinuousExtensionUp : Type where
  | mk (S W D F U L H C P N : BHist) : CauchyContinuousExtensionUp
  deriving DecidableEq

def cauchyContinuousExtensionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuousExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuousExtensionEncodeBHist h

def cauchyContinuousExtensionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuousExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuousExtensionDecodeBHist tail)

private theorem CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContinuousExtensionFields : CauchyContinuousExtensionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuousExtensionUp.mk S W D F U L H C P N => [S, W, D, F, U, L, H, C, P, N]

def cauchyContinuousExtensionToEventFlow : CauchyContinuousExtensionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyContinuousExtensionFields x).map cauchyContinuousExtensionEncodeBHist

private def cauchyContinuousExtensionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyContinuousExtensionEventAt index rest

def cauchyContinuousExtensionFromEventFlow (ef : EventFlow) :
    Option CauchyContinuousExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyContinuousExtensionUp.mk
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 0 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 1 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 2 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 3 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 4 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 5 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 6 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 7 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 8 ef))
      (cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEventAt 9 ef)))

private theorem cauchyContinuousExtension_mk_congr
    {S S' W W' D D' F F' U U' L L' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hW : W' = W) (hD : D' = D) (hF : F' = F)
    (hU : U' = U) (hL : L' = L) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    CauchyContinuousExtensionUp.mk S' W' D' F' U' L' H' C' P' N' =
      CauchyContinuousExtensionUp.mk S W D F U L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hW
  cases hD
  cases hF
  cases hU
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyContinuousExtensionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyContinuousExtensionUp,
      cauchyContinuousExtensionFromEventFlow (cauchyContinuousExtensionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D F U L H C P N =>
      exact
        congrArg some
          (cauchyContinuousExtension_mk_congr
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode S)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode W)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode D)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode F)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode U)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode L)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode H)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode C)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode P)
            (CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode N))

private theorem cauchyContinuousExtensionToEventFlow_injective
    {x y : CauchyContinuousExtensionUp} :
    cauchyContinuousExtensionToEventFlow x = cauchyContinuousExtensionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuousExtensionFromEventFlow (cauchyContinuousExtensionToEventFlow x) =
        cauchyContinuousExtensionFromEventFlow (cauchyContinuousExtensionToEventFlow y) :=
    congrArg cauchyContinuousExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyContinuousExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyContinuousExtensionTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyContinuousExtension_field_faithful :
    ∀ x y : CauchyContinuousExtensionUp,
      cauchyContinuousExtensionFields x = cauchyContinuousExtensionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S W D F U L H C P N =>
      cases y with
      | mk S' W' D' F' U' L' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyContinuousExtensionBHistCarrier :
    BHistCarrier CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuousExtensionToEventFlow
  fromEventFlow := cauchyContinuousExtensionFromEventFlow

instance cauchyContinuousExtensionChapterTasteGate :
    ChapterTasteGate CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyContinuousExtensionFromEventFlow (cauchyContinuousExtensionToEventFlow x) =
      some x
    exact CauchyContinuousExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyContinuousExtensionToEventFlow_injective heq)

instance cauchyContinuousExtensionFieldFaithful :
    FieldFaithful CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyContinuousExtensionFields
  field_faithful := cauchyContinuousExtension_field_faithful

instance cauchyContinuousExtensionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyContinuousExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyContinuousExtensionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyContinuousExtensionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyContinuousExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyContinuousExtensionChapterTasteGate

theorem CauchyContinuousExtensionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyContinuousExtensionUp) ∧
      Nonempty (FieldFaithful CauchyContinuousExtensionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyContinuousExtensionUp) ∧
      (∀ h : BHist,
        cauchyContinuousExtensionDecodeBHist (cauchyContinuousExtensionEncodeBHist h) = h) ∧
      (∀ x : CauchyContinuousExtensionUp,
        cauchyContinuousExtensionFromEventFlow (cauchyContinuousExtensionToEventFlow x) =
          some x) ∧
      (∀ x y : CauchyContinuousExtensionUp,
        cauchyContinuousExtensionToEventFlow x = cauchyContinuousExtensionToEventFlow y →
          x = y) ∧
      cauchyContinuousExtensionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨cauchyContinuousExtensionChapterTasteGate⟩
  constructor
  · exact ⟨cauchyContinuousExtensionFieldFaithful⟩
  constructor
  · exact ⟨cauchyContinuousExtensionNontrivial⟩
  constructor
  · exact CauchyContinuousExtensionTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyContinuousExtensionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyContinuousExtensionToEventFlow_injective heq
  · rfl

end TasteGate
end BEDC.Derived.CauchyContinuousExtensionUp
