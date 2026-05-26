import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySpreadUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySpreadUp : Type where
  | mk (S W T R L H C P N : BHist) : RegularCauchySpreadUp
  deriving DecidableEq

def regularCauchySpreadEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySpreadEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySpreadEncodeBHist h

def regularCauchySpreadDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySpreadDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySpreadDecodeBHist tail)

private theorem RegularCauchySpreadTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def RegularCauchySpreadTasteGate_single_carrier_alignment_fields :
    RegularCauchySpreadUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySpreadUp.mk S W T R L H C P N => [S, W, T, R, L, H, C, P, N]

def regularCauchySpreadToEventFlow : RegularCauchySpreadUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySpreadUp.mk S W T R L H C P N =>
      [regularCauchySpreadEncodeBHist S, regularCauchySpreadEncodeBHist W,
        regularCauchySpreadEncodeBHist T, regularCauchySpreadEncodeBHist R,
        regularCauchySpreadEncodeBHist L, regularCauchySpreadEncodeBHist H,
        regularCauchySpreadEncodeBHist C, regularCauchySpreadEncodeBHist P,
        regularCauchySpreadEncodeBHist N]

private def regularCauchySpreadEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySpreadEventAtDefault index rest

def regularCauchySpreadFromEventFlow : EventFlow → Option RegularCauchySpreadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchySpreadUp.mk
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 0 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 1 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 2 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 3 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 4 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 5 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 6 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 7 ef))
        (regularCauchySpreadDecodeBHist (regularCauchySpreadEventAtDefault 8 ef)))

private theorem RegularCauchySpreadTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySpreadUp,
      regularCauchySpreadFromEventFlow (regularCauchySpreadToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W T R L H C P N =>
      simp only [regularCauchySpreadToEventFlow, regularCauchySpreadFromEventFlow,
        regularCauchySpreadEventAtDefault,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode S,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode W,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode T,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode R,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode L,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode H,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode C,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode P,
        RegularCauchySpreadTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchySpreadTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySpreadUp} :
    regularCauchySpreadToEventFlow x = regularCauchySpreadToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk S₁ W₁ T₁ R₁ L₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ W₂ T₂ R₂ L₂ H₂ C₂ P₂ N₂ =>
          simp only [regularCauchySpreadToEventFlow] at heq
          injection heq with hS tail0
          injection tail0 with hW tail1
          injection tail1 with hT tail2
          injection tail2 with hR tail3
          injection tail3 with hL tail4
          injection tail4 with hH tail5
          injection tail5 with hC tail6
          injection tail6 with hP tail7
          injection tail7 with hN _
          have sameS : S₁ = S₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hS
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode S₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode S₂] at decoded
            exact decoded
          have sameW : W₁ = W₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hW
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode W₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode W₂] at decoded
            exact decoded
          have sameT : T₁ = T₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hT
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode T₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode T₂] at decoded
            exact decoded
          have sameR : R₁ = R₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hR
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode R₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode R₂] at decoded
            exact decoded
          have sameL : L₁ = L₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hL
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode L₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode L₂] at decoded
            exact decoded
          have sameH : H₁ = H₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hH
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode H₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode H₂] at decoded
            exact decoded
          have sameC : C₁ = C₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hC
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode C₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode C₂] at decoded
            exact decoded
          have sameP : P₁ = P₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hP
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode P₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode P₂] at decoded
            exact decoded
          have sameN : N₁ = N₂ := by
            have decoded := congrArg regularCauchySpreadDecodeBHist hN
            rw [RegularCauchySpreadTasteGate_single_carrier_alignment_decode N₁,
              RegularCauchySpreadTasteGate_single_carrier_alignment_decode N₂] at decoded
            exact decoded
          subst sameS
          subst sameW
          subst sameT
          subst sameR
          subst sameL
          subst sameH
          subst sameC
          subst sameP
          subst sameN
          rfl

instance regularCauchySpreadBHistCarrier : BHistCarrier RegularCauchySpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySpreadToEventFlow
  fromEventFlow := regularCauchySpreadFromEventFlow

instance regularCauchySpreadChapterTasteGate : ChapterTasteGate RegularCauchySpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySpreadFromEventFlow (regularCauchySpreadToEventFlow x) = some x
    exact RegularCauchySpreadTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchySpreadTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchySpreadNontrivial : Nontrivial RegularCauchySpreadUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySpreadUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchySpreadUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchySpreadTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchySpreadUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySpreadChapterTasteGate

theorem RegularCauchySpreadTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchySpreadDecodeBHist (regularCauchySpreadEncodeBHist h) = h) ∧
      RegularCauchySpreadTasteGate_single_carrier_alignment_fields
          (RegularCauchySpreadUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] ∧
      regularCauchySpreadEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact RegularCauchySpreadTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.RegularCauchySpreadUp.TasteGate
