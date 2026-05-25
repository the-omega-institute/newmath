import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyersUlamStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyersUlamStabilityUp : Type where
  | mk (A W L M R H C P N : BHist) : HyersUlamStabilityUp
  deriving DecidableEq

def hyersUlamStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyersUlamStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyersUlamStabilityEncodeBHist h

def hyersUlamStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyersUlamStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyersUlamStabilityDecodeBHist tail)

private theorem HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyersUlamStabilityToEventFlow : HyersUlamStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HyersUlamStabilityUp.mk A W L M R H C P N =>
      [hyersUlamStabilityEncodeBHist A,
        hyersUlamStabilityEncodeBHist W,
        hyersUlamStabilityEncodeBHist L,
        hyersUlamStabilityEncodeBHist M,
        hyersUlamStabilityEncodeBHist R,
        hyersUlamStabilityEncodeBHist H,
        hyersUlamStabilityEncodeBHist C,
        hyersUlamStabilityEncodeBHist P,
        hyersUlamStabilityEncodeBHist N]

private def hyersUlamStabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyersUlamStabilityEventAtDefault index rest

def hyersUlamStabilityFromEventFlow (ef : EventFlow) : Option HyersUlamStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyersUlamStabilityUp.mk
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 0 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 1 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 2 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 3 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 4 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 5 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 6 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 7 ef))
      (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEventAtDefault 8 ef)))

private theorem HyersUlamStabilityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HyersUlamStabilityUp,
      hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A W L M R H C P N =>
      change
        some
          (HyersUlamStabilityUp.mk
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist A))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist W))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist L))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist M))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist R))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist H))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist C))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist P))
            (hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist N))) =
          some (HyersUlamStabilityUp.mk A W L M R H C P N)
      rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode A,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode W,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode L,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode M,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode R,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode H,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode C,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode P,
        HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyersUlamStabilityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HyersUlamStabilityUp} :
    hyersUlamStabilityToEventFlow x = hyersUlamStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk A₁ W₁ L₁ M₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ W₂ L₂ M₂ R₂ H₂ C₂ P₂ N₂ =>
          injection heq with hA tail0
          injection tail0 with hW tail1
          injection tail1 with hL tail2
          injection tail2 with hM tail3
          injection tail3 with hR tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          have eA : A₁ = A₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hA
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode A₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode A₂] at h
            exact h
          have eW : W₁ = W₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hW
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode W₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode W₂] at h
            exact h
          have eL : L₁ = L₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hL
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode L₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode L₂] at h
            exact h
          have eM : M₁ = M₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hM
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode M₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode M₂] at h
            exact h
          have eR : R₁ = R₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hR
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode R₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode R₂] at h
            exact h
          have eH : H₁ = H₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hH
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode H₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode H₂] at h
            exact h
          have eC : C₁ = C₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hC
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode C₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode C₂] at h
            exact h
          have eP : P₁ = P₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hP
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode P₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode P₂] at h
            exact h
          have eN : N₁ = N₂ := by
            have h := congrArg hyersUlamStabilityDecodeBHist hN
            rw [HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode N₁,
              HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode N₂] at h
            exact h
          subst eA
          subst eW
          subst eL
          subst eM
          subst eR
          subst eH
          subst eC
          subst eP
          subst eN
          rfl

instance hyersUlamStabilityBHistCarrier : BHistCarrier HyersUlamStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyersUlamStabilityToEventFlow
  fromEventFlow := hyersUlamStabilityFromEventFlow

instance hyersUlamStabilityChapterTasteGate : ChapterTasteGate HyersUlamStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow x) = some x
    exact HyersUlamStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyersUlamStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HyersUlamStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyersUlamStabilityChapterTasteGate

theorem HyersUlamStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyersUlamStabilityDecodeBHist (hyersUlamStabilityEncodeBHist h) = h) ∧
      (∀ x : HyersUlamStabilityUp,
        hyersUlamStabilityFromEventFlow (hyersUlamStabilityToEventFlow x) = some x) ∧
        (∀ x y : HyersUlamStabilityUp,
          hyersUlamStabilityToEventFlow x = hyersUlamStabilityToEventFlow y → x = y) ∧
          hyersUlamStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow ChapterTasteGate
  exact
    ⟨HyersUlamStabilityTasteGate_single_carrier_alignment_decode_encode,
      HyersUlamStabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        HyersUlamStabilityTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HyersUlamStabilityUp
