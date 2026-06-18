import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.CousinGaugeCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive CousinGaugeCoverUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (D T F S H C P N : BHist) → CousinGaugeCoverUp

def cousinGaugeCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cousinGaugeCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cousinGaugeCoverEncodeBHist h

def cousinGaugeCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cousinGaugeCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cousinGaugeCoverDecodeBHist tail)

private theorem CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cousinGaugeCoverFields : CousinGaugeCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CousinGaugeCoverUp.mk D T F S H C P N => [D, T, F, S, H, C, P, N]

def cousinGaugeCoverToEventFlow : CousinGaugeCoverUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cousinGaugeCoverFields x).map cousinGaugeCoverEncodeBHist

private def cousinGaugeCoverEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cousinGaugeCoverEventAtDefault index rest

def cousinGaugeCoverFromEventFlow (ef : EventFlow) : Option CousinGaugeCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CousinGaugeCoverUp.mk
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 0 ef))
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 1 ef))
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 2 ef))
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 3 ef))
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 4 ef))
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 5 ef))
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 6 ef))
      (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEventAtDefault 7 ef)))

private theorem CousinGaugeCoverTasteGate_single_carrier_alignment_round_trip
    (x : CousinGaugeCoverUp) :
    cousinGaugeCoverFromEventFlow (cousinGaugeCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D T F S H C P N =>
      change
        some
          (CousinGaugeCoverUp.mk
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist D))
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist T))
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist F))
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist S))
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist H))
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist C))
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist P))
            (cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist N))) =
          some (CousinGaugeCoverUp.mk D T F S H C P N)
      rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode D,
        CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode T,
        CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode F,
        CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode S,
        CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode H,
        CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode C,
        CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode P,
        CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem CousinGaugeCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CousinGaugeCoverUp} :
    cousinGaugeCoverToEventFlow x = cousinGaugeCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk D₁ T₁ F₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D₂ T₂ F₂ S₂ H₂ C₂ P₂ N₂ =>
          change
            [cousinGaugeCoverEncodeBHist D₁, cousinGaugeCoverEncodeBHist T₁,
              cousinGaugeCoverEncodeBHist F₁, cousinGaugeCoverEncodeBHist S₁,
              cousinGaugeCoverEncodeBHist H₁, cousinGaugeCoverEncodeBHist C₁,
              cousinGaugeCoverEncodeBHist P₁, cousinGaugeCoverEncodeBHist N₁] =
            [cousinGaugeCoverEncodeBHist D₂, cousinGaugeCoverEncodeBHist T₂,
              cousinGaugeCoverEncodeBHist F₂, cousinGaugeCoverEncodeBHist S₂,
              cousinGaugeCoverEncodeBHist H₂, cousinGaugeCoverEncodeBHist C₂,
              cousinGaugeCoverEncodeBHist P₂, cousinGaugeCoverEncodeBHist N₂] at heq
          injection heq with hD rest₁
          injection rest₁ with hT rest₂
          injection rest₂ with hF rest₃
          injection rest₃ with hS rest₄
          injection rest₄ with hH rest₅
          injection rest₅ with hC rest₆
          injection rest₆ with hP rest₇
          injection rest₇ with hN _
          have dD : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist D₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist D₂) :=
            congrArg cousinGaugeCoverDecodeBHist hD
          have dT : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist T₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist T₂) :=
            congrArg cousinGaugeCoverDecodeBHist hT
          have dF : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist F₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist F₂) :=
            congrArg cousinGaugeCoverDecodeBHist hF
          have dS : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist S₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist S₂) :=
            congrArg cousinGaugeCoverDecodeBHist hS
          have dH : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist H₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist H₂) :=
            congrArg cousinGaugeCoverDecodeBHist hH
          have dC : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist C₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist C₂) :=
            congrArg cousinGaugeCoverDecodeBHist hC
          have dP : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist P₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist P₂) :=
            congrArg cousinGaugeCoverDecodeBHist hP
          have dN : cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist N₁) =
              cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist N₂) :=
            congrArg cousinGaugeCoverDecodeBHist hN
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode D₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode D₂] at dD
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode T₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode T₂] at dT
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode F₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode F₂] at dF
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode S₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode S₂] at dS
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode H₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode H₂] at dH
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode C₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode C₂] at dC
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode P₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode P₂] at dP
          rw [CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode N₁,
            CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode N₂] at dN
          cases dD
          cases dT
          cases dF
          cases dS
          cases dH
          cases dC
          cases dP
          cases dN
          rfl

theorem CousinGaugeCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, cousinGaugeCoverDecodeBHist (cousinGaugeCoverEncodeBHist h) = h) ∧
      (∀ x : CousinGaugeCoverUp,
        cousinGaugeCoverFromEventFlow (cousinGaugeCoverToEventFlow x) = some x) ∧
        (∀ x y : CousinGaugeCoverUp,
          cousinGaugeCoverToEventFlow x = cousinGaugeCoverToEventFlow y → x = y) ∧
          cousinGaugeCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CousinGaugeCoverTasteGate_single_carrier_alignment_decode_encode,
      CousinGaugeCoverTasteGate_single_carrier_alignment_round_trip,
      fun _x _y => CousinGaugeCoverTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.CousinGaugeCoverUp
