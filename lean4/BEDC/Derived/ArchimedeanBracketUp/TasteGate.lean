import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanBracketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanBracketUp : Type where
  | mk (R L U D S Q H C P N : BHist) : ArchimedeanBracketUp
  deriving DecidableEq

def archimedeanBracketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanBracketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanBracketEncodeBHist h

def archimedeanBracketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanBracketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanBracketDecodeBHist tail)

private theorem ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanBracketToEventFlow : ArchimedeanBracketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanBracketUp.mk R L U D S Q H C P N =>
      [archimedeanBracketEncodeBHist R,
        archimedeanBracketEncodeBHist L,
        archimedeanBracketEncodeBHist U,
        archimedeanBracketEncodeBHist D,
        archimedeanBracketEncodeBHist S,
        archimedeanBracketEncodeBHist Q,
        archimedeanBracketEncodeBHist H,
        archimedeanBracketEncodeBHist C,
        archimedeanBracketEncodeBHist P,
        archimedeanBracketEncodeBHist N]

private def archimedeanBracketEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => archimedeanBracketEventAtDefault index rest

def archimedeanBracketFromEventFlow (ef : EventFlow) : Option ArchimedeanBracketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArchimedeanBracketUp.mk
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 0 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 1 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 2 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 3 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 4 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 5 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 6 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 7 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 8 ef))
      (archimedeanBracketDecodeBHist (archimedeanBracketEventAtDefault 9 ef)))

private theorem ArchimedeanBracketTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArchimedeanBracketUp,
      archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R L U D S Q H C P N =>
      change
        some
          (ArchimedeanBracketUp.mk
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist R))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist L))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist U))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist D))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist S))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist Q))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist H))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist C))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist P))
            (archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist N))) =
          some (ArchimedeanBracketUp.mk R L U D S Q H C P N)
      rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode R,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode L,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode U,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode D,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode S,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode Q,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode H,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode C,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode P,
        ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode N]

private theorem ArchimedeanBracketTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ArchimedeanBracketUp} :
    archimedeanBracketToEventFlow x = archimedeanBracketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk R₁ L₁ U₁ D₁ S₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ L₂ U₂ D₂ S₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection heq with hR tail0
          injection tail0 with hL tail1
          injection tail1 with hU tail2
          injection tail2 with hD tail3
          injection tail3 with hS tail4
          injection tail4 with hQ tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          have eR : R₁ = R₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hR
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode R₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode R₂] at h
            exact h
          have eL : L₁ = L₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hL
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode L₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode L₂] at h
            exact h
          have eU : U₁ = U₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hU
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode U₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode U₂] at h
            exact h
          have eD : D₁ = D₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hD
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode D₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode D₂] at h
            exact h
          have eS : S₁ = S₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hS
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode S₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode S₂] at h
            exact h
          have eQ : Q₁ = Q₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hQ
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode Q₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode Q₂] at h
            exact h
          have eH : H₁ = H₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hH
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode H₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode H₂] at h
            exact h
          have eC : C₁ = C₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hC
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode C₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode C₂] at h
            exact h
          have eP : P₁ = P₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hP
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode P₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode P₂] at h
            exact h
          have eN : N₁ = N₂ := by
            have h := congrArg archimedeanBracketDecodeBHist hN
            rw [ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode N₁,
              ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode N₂] at h
            exact h
          subst eR
          subst eL
          subst eU
          subst eD
          subst eS
          subst eQ
          subst eH
          subst eC
          subst eP
          subst eN
          rfl

instance archimedeanBracketBHistCarrier : BHistCarrier ArchimedeanBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanBracketToEventFlow
  fromEventFlow := archimedeanBracketFromEventFlow

instance archimedeanBracketChapterTasteGate : ChapterTasteGate ArchimedeanBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow x) = some x
    exact ArchimedeanBracketTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ArchimedeanBracketTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ArchimedeanBracketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanBracketChapterTasteGate

theorem ArchimedeanBracketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      archimedeanBracketDecodeBHist (archimedeanBracketEncodeBHist h) = h) ∧
      (∀ x : ArchimedeanBracketUp,
        archimedeanBracketFromEventFlow (archimedeanBracketToEventFlow x) = some x) ∧
        (∀ x y : ArchimedeanBracketUp,
          archimedeanBracketToEventFlow x = archimedeanBracketToEventFlow y → x = y) ∧
          archimedeanBracketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow ChapterTasteGate
  exact
    ⟨ArchimedeanBracketTasteGate_single_carrier_alignment_decode_encode,
      ArchimedeanBracketTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ArchimedeanBracketTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ArchimedeanBracketUp
