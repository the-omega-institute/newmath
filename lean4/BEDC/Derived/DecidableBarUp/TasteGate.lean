import BEDC.Derived.DecidableBarUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.DecidableBarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

inductive DecidableBarUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk : (C S W R D H T P N : BHist) → DecidableBarUp

def decidableBarEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: decidableBarEncodeBHist h
  | BHist.e1 h => BMark.b1 :: decidableBarEncodeBHist h

def decidableBarDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decidableBarDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decidableBarDecodeBHist tail)

private theorem DecidableBarTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, decidableBarDecodeBHist (decidableBarEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def decidableBarFields : DecidableBarUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DecidableBarUp.mk C S W R D H T P N => [C, S, W, R, D, H, T, P, N]

def decidableBarToEventFlow : DecidableBarUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (decidableBarFields x).map decidableBarEncodeBHist

private def decidableBarEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => decidableBarEventAtDefault index rest

def decidableBarFromEventFlow (ef : EventFlow) : Option DecidableBarUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DecidableBarUp.mk
      (decidableBarDecodeBHist (decidableBarEventAtDefault 0 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 1 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 2 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 3 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 4 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 5 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 6 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 7 ef))
      (decidableBarDecodeBHist (decidableBarEventAtDefault 8 ef)))

private theorem DecidableBarTasteGate_single_carrier_alignment_round_trip
    (x : DecidableBarUp) :
    decidableBarFromEventFlow (decidableBarToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C S W R D H T P N =>
      change
        some
          (DecidableBarUp.mk
            (decidableBarDecodeBHist (decidableBarEncodeBHist C))
            (decidableBarDecodeBHist (decidableBarEncodeBHist S))
            (decidableBarDecodeBHist (decidableBarEncodeBHist W))
            (decidableBarDecodeBHist (decidableBarEncodeBHist R))
            (decidableBarDecodeBHist (decidableBarEncodeBHist D))
            (decidableBarDecodeBHist (decidableBarEncodeBHist H))
            (decidableBarDecodeBHist (decidableBarEncodeBHist T))
            (decidableBarDecodeBHist (decidableBarEncodeBHist P))
            (decidableBarDecodeBHist (decidableBarEncodeBHist N))) =
          some (DecidableBarUp.mk C S W R D H T P N)
      rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode C,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode S,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode W,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode R,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode D,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode H,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode T,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode P,
        DecidableBarTasteGate_single_carrier_alignment_decode_encode N]

private theorem DecidableBarTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DecidableBarUp} :
    decidableBarToEventFlow x = decidableBarToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk C₁ S₁ W₁ R₁ D₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk C₂ S₂ W₂ R₂ D₂ H₂ T₂ P₂ N₂ =>
          change
            [decidableBarEncodeBHist C₁, decidableBarEncodeBHist S₁,
              decidableBarEncodeBHist W₁, decidableBarEncodeBHist R₁,
              decidableBarEncodeBHist D₁, decidableBarEncodeBHist H₁,
              decidableBarEncodeBHist T₁, decidableBarEncodeBHist P₁,
              decidableBarEncodeBHist N₁] =
            [decidableBarEncodeBHist C₂, decidableBarEncodeBHist S₂,
              decidableBarEncodeBHist W₂, decidableBarEncodeBHist R₂,
              decidableBarEncodeBHist D₂, decidableBarEncodeBHist H₂,
              decidableBarEncodeBHist T₂, decidableBarEncodeBHist P₂,
              decidableBarEncodeBHist N₂] at heq
          injection heq with hC rest₁
          injection rest₁ with hS rest₂
          injection rest₂ with hW rest₃
          injection rest₃ with hR rest₄
          injection rest₄ with hD rest₅
          injection rest₅ with hH rest₆
          injection rest₆ with hT rest₇
          injection rest₇ with hP rest₈
          injection rest₈ with hN _
          have dC : decidableBarDecodeBHist (decidableBarEncodeBHist C₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist C₂) :=
            congrArg decidableBarDecodeBHist hC
          have dS : decidableBarDecodeBHist (decidableBarEncodeBHist S₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist S₂) :=
            congrArg decidableBarDecodeBHist hS
          have dW : decidableBarDecodeBHist (decidableBarEncodeBHist W₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist W₂) :=
            congrArg decidableBarDecodeBHist hW
          have dR : decidableBarDecodeBHist (decidableBarEncodeBHist R₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist R₂) :=
            congrArg decidableBarDecodeBHist hR
          have dD : decidableBarDecodeBHist (decidableBarEncodeBHist D₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist D₂) :=
            congrArg decidableBarDecodeBHist hD
          have dH : decidableBarDecodeBHist (decidableBarEncodeBHist H₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist H₂) :=
            congrArg decidableBarDecodeBHist hH
          have dT : decidableBarDecodeBHist (decidableBarEncodeBHist T₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist T₂) :=
            congrArg decidableBarDecodeBHist hT
          have dP : decidableBarDecodeBHist (decidableBarEncodeBHist P₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist P₂) :=
            congrArg decidableBarDecodeBHist hP
          have dN : decidableBarDecodeBHist (decidableBarEncodeBHist N₁) =
              decidableBarDecodeBHist (decidableBarEncodeBHist N₂) :=
            congrArg decidableBarDecodeBHist hN
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode C₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode C₂] at dC
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode S₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode S₂] at dS
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode W₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode W₂] at dW
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode R₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode R₂] at dR
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode D₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode D₂] at dD
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode H₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode H₂] at dH
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode T₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode T₂] at dT
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode P₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode P₂] at dP
          rw [DecidableBarTasteGate_single_carrier_alignment_decode_encode N₁,
            DecidableBarTasteGate_single_carrier_alignment_decode_encode N₂] at dN
          cases dC
          cases dS
          cases dW
          cases dR
          cases dD
          cases dH
          cases dT
          cases dP
          cases dN
          rfl

theorem DecidableBarTasteGate_single_carrier_alignment :
    (∀ h : BHist, decidableBarDecodeBHist (decidableBarEncodeBHist h) = h) ∧
      (∀ x : DecidableBarUp, decidableBarFromEventFlow (decidableBarToEventFlow x) = some x) ∧
        (∀ x y : DecidableBarUp, decidableBarToEventFlow x = decidableBarToEventFlow y → x = y) ∧
          decidableBarEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DecidableBarTasteGate_single_carrier_alignment_decode_encode,
      DecidableBarTasteGate_single_carrier_alignment_round_trip,
      fun _x _y => DecidableBarTasteGate_single_carrier_alignment_toEventFlow_injective,
      rfl⟩

end BEDC.Derived.DecidableBarUp
