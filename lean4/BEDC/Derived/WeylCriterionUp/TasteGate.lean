import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.WeylCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive WeylCriterionUp : Type where
  | mk (I F Z U S R D E H C P N : BHist) : WeylCriterionUp

def weylCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weylCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weylCriterionEncodeBHist h

def weylCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weylCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weylCriterionDecodeBHist tail)

def weylCriterionRawAt : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _, 0 => head
  | _ :: tail, Nat.succ n => weylCriterionRawAt tail n

private theorem weylCriterionDecode_encode_bhist :
    ∀ h : BHist, weylCriterionDecodeBHist (weylCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem WeylCriterionTasteGate_single_carrier_alignment_mk_congr
    {I₁ I₂ F₁ F₂ Z₁ Z₂ U₁ U₂ S₁ S₂ R₁ R₂ D₁ D₂ E₁ E₂ H₁ H₂ C₁ C₂
      P₁ P₂ N₁ N₂ : BHist} :
    I₁ = I₂ → F₁ = F₂ → Z₁ = Z₂ → U₁ = U₂ → S₁ = S₂ → R₁ = R₂ →
      D₁ = D₂ → E₁ = E₂ → H₁ = H₂ → C₁ = C₂ → P₁ = P₂ → N₁ = N₂ →
        WeylCriterionUp.mk I₁ F₁ Z₁ U₁ S₁ R₁ D₁ E₁ H₁ C₁ P₁ N₁ =
          WeylCriterionUp.mk I₂ F₂ Z₂ U₂ S₂ R₂ D₂ E₂ H₂ C₂ P₂ N₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hI hF hZ hU hS hR hD hE hH hC hP hN
  cases hI
  cases hF
  cases hZ
  cases hU
  cases hS
  cases hR
  cases hD
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def weylCriterionToEventFlow : WeylCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WeylCriterionUp.mk I F Z U S R D E H C P N =>
      [weylCriterionEncodeBHist I,
        weylCriterionEncodeBHist F,
        weylCriterionEncodeBHist Z,
        weylCriterionEncodeBHist U,
        weylCriterionEncodeBHist S,
        weylCriterionEncodeBHist R,
        weylCriterionEncodeBHist D,
        weylCriterionEncodeBHist E,
        weylCriterionEncodeBHist H,
        weylCriterionEncodeBHist C,
        weylCriterionEncodeBHist P,
        weylCriterionEncodeBHist N]

def weylCriterionFromEventFlow : EventFlow → Option WeylCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (WeylCriterionUp.mk
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 0))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 1))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 2))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 3))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 4))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 5))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 6))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 7))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 8))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 9))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 10))
          (weylCriterionDecodeBHist (weylCriterionRawAt flow 11)))

private theorem WeylCriterionTasteGate_single_carrier_alignment_round_trip
    (x : WeylCriterionUp) :
    weylCriterionFromEventFlow (weylCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I F Z U S R D E H C P N =>
      change
        some
          (WeylCriterionUp.mk
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist I))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist F))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist Z))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist U))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist S))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist R))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist D))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist E))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist H))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist C))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist P))
            (weylCriterionDecodeBHist (weylCriterionEncodeBHist N))) =
          some (WeylCriterionUp.mk I F Z U S R D E H C P N)
      rw [weylCriterionDecode_encode_bhist I, weylCriterionDecode_encode_bhist F,
        weylCriterionDecode_encode_bhist Z, weylCriterionDecode_encode_bhist U,
        weylCriterionDecode_encode_bhist S, weylCriterionDecode_encode_bhist R,
        weylCriterionDecode_encode_bhist D, weylCriterionDecode_encode_bhist E,
        weylCriterionDecode_encode_bhist H, weylCriterionDecode_encode_bhist C,
        weylCriterionDecode_encode_bhist P, weylCriterionDecode_encode_bhist N]

private theorem WeylCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : WeylCriterionUp} :
    weylCriterionToEventFlow x = weylCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weylCriterionFromEventFlow (weylCriterionToEventFlow x) =
        weylCriterionFromEventFlow (weylCriterionToEventFlow y) :=
    congrArg weylCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (WeylCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (WeylCriterionTasteGate_single_carrier_alignment_round_trip y)))

theorem WeylCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, weylCriterionDecodeBHist (weylCriterionEncodeBHist h) = h) ∧
      (∀ x : WeylCriterionUp,
        weylCriterionFromEventFlow (weylCriterionToEventFlow x) = some x) ∧
        (∀ x y : WeylCriterionUp,
          weylCriterionToEventFlow x = weylCriterionToEventFlow y → x = y) ∧
          weylCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨weylCriterionDecode_encode_bhist,
      WeylCriterionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => WeylCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.WeylCriterionUp
