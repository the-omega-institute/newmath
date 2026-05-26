import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubsequenceStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubsequenceStabilityUp : Type where
  | mk (S T W D R E H C P N : BHist) : RegularCauchySubsequenceStabilityUp
  deriving DecidableEq

def regularCauchySubsequenceStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubsequenceStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubsequenceStabilityEncodeBHist h

def regularCauchySubsequenceStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubsequenceStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubsequenceStabilityDecodeBHist tail)

private theorem regularCauchySubsequenceStabilityDecode_encode :
    ∀ h : BHist,
      regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySubsequenceStabilityFields :
    RegularCauchySubsequenceStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N =>
      [S, T, W, D, R, E, H, C, P, N]

def regularCauchySubsequenceStabilityToEventFlow :
    RegularCauchySubsequenceStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchySubsequenceStabilityFields x).map
        regularCauchySubsequenceStabilityEncodeBHist

private def regularCauchySubsequenceStabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchySubsequenceStabilityEventAtDefault index rest

def regularCauchySubsequenceStabilityFromEventFlow
    (ef : EventFlow) : Option RegularCauchySubsequenceStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySubsequenceStabilityUp.mk
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 0 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 1 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 2 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 3 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 4 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 5 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 6 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 7 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 8 ef))
      (regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEventAtDefault 9 ef)))

private theorem regularCauchySubsequenceStability_round_trip :
    ∀ x : RegularCauchySubsequenceStabilityUp,
      regularCauchySubsequenceStabilityFromEventFlow
        (regularCauchySubsequenceStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W D R E H C P N =>
      change
        some
          (RegularCauchySubsequenceStabilityUp.mk
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist S))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist T))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist W))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist D))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist R))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist E))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist H))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist C))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist P))
            (regularCauchySubsequenceStabilityDecodeBHist
              (regularCauchySubsequenceStabilityEncodeBHist N))) =
          some (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N)
      rw [regularCauchySubsequenceStabilityDecode_encode S,
        regularCauchySubsequenceStabilityDecode_encode T,
        regularCauchySubsequenceStabilityDecode_encode W,
        regularCauchySubsequenceStabilityDecode_encode D,
        regularCauchySubsequenceStabilityDecode_encode R,
        regularCauchySubsequenceStabilityDecode_encode E,
        regularCauchySubsequenceStabilityDecode_encode H,
        regularCauchySubsequenceStabilityDecode_encode C,
        regularCauchySubsequenceStabilityDecode_encode P,
        regularCauchySubsequenceStabilityDecode_encode N]

private theorem regularCauchySubsequenceStabilityToEventFlow_injective
    {x y : RegularCauchySubsequenceStabilityUp} :
    regularCauchySubsequenceStabilityToEventFlow x =
      regularCauchySubsequenceStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySubsequenceStabilityFromEventFlow
          (regularCauchySubsequenceStabilityToEventFlow x) =
        regularCauchySubsequenceStabilityFromEventFlow
          (regularCauchySubsequenceStabilityToEventFlow y) :=
    congrArg regularCauchySubsequenceStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchySubsequenceStability_round_trip x).symm
      (Eq.trans hread (regularCauchySubsequenceStability_round_trip y)))

instance regularCauchySubsequenceStabilityBHistCarrier :
    BHistCarrier RegularCauchySubsequenceStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubsequenceStabilityToEventFlow
  fromEventFlow := regularCauchySubsequenceStabilityFromEventFlow

instance regularCauchySubsequenceStabilityChapterTasteGate :
    ChapterTasteGate RegularCauchySubsequenceStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubsequenceStabilityFromEventFlow
        (regularCauchySubsequenceStabilityToEventFlow x) = some x
    exact regularCauchySubsequenceStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubsequenceStabilityToEventFlow_injective heq)

instance regularCauchySubsequenceStabilityFieldFaithful :
    FieldFaithful RegularCauchySubsequenceStabilityUp where
  fields := regularCauchySubsequenceStabilityFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk S₁ T₁ W₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ W₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
        change [S₁, T₁, W₁, D₁, R₁, E₁, H₁, C₁, P₁, N₁] =
          [S₂, T₂, W₂, D₂, R₂, E₂, H₂, C₂, P₂, N₂] at h
        injection h with hS tail0
        injection tail0 with hT tail1
        injection tail1 with hW tail2
        injection tail2 with hD tail3
        injection tail3 with hR tail4
        injection tail4 with hE tail5
        injection tail5 with hH tail6
        injection tail6 with hC tail7
        injection tail7 with hP tail8
        injection tail8 with hN _
        subst hS
        subst hT
        subst hW
        subst hD
        subst hR
        subst hE
        subst hH
        subst hC
        subst hP
        subst hN
        rfl

instance regularCauchySubsequenceStabilityNontrivial :
    Nontrivial RegularCauchySubsequenceStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchySubsequenceStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchySubsequenceStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchySubsequenceStabilityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySubsequenceStabilityDecodeBHist
        (regularCauchySubsequenceStabilityEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySubsequenceStabilityUp,
        regularCauchySubsequenceStabilityFromEventFlow
          (regularCauchySubsequenceStabilityToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchySubsequenceStabilityUp,
        regularCauchySubsequenceStabilityToEventFlow x =
          regularCauchySubsequenceStabilityToEventFlow y → x = y) ∧
      regularCauchySubsequenceStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchySubsequenceStabilityDecode_encode,
      regularCauchySubsequenceStability_round_trip,
      fun _ _ heq => regularCauchySubsequenceStabilityToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchySubsequenceStabilityUp
