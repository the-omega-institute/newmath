import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MaterialityOrbitEscapeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MaterialityOrbitEscapeUp : Type where
  | mk (O F I R S T H C P N : BHist) : MaterialityOrbitEscapeUp
  deriving DecidableEq

def materialityOrbitEscapeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: materialityOrbitEscapeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: materialityOrbitEscapeEncodeBHist h

def materialityOrbitEscapeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (materialityOrbitEscapeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (materialityOrbitEscapeDecodeBHist tail)

private theorem materialityOrbitEscapeDecode_encode :
    ∀ h : BHist,
      materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def materialityOrbitEscapeFields : MaterialityOrbitEscapeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MaterialityOrbitEscapeUp.mk O F I R S T H C P N => [O, F, I, R, S, T, H, C, P, N]

def materialityOrbitEscapeToEventFlow : MaterialityOrbitEscapeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (materialityOrbitEscapeFields x).map materialityOrbitEscapeEncodeBHist

private def materialityOrbitEscapeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => materialityOrbitEscapeEventAt index rest

def materialityOrbitEscapeFromEventFlow
    (ef : EventFlow) : Option MaterialityOrbitEscapeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MaterialityOrbitEscapeUp.mk
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 0 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 1 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 2 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 3 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 4 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 5 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 6 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 7 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 8 ef))
      (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEventAt 9 ef)))

private theorem materialityOrbitEscape_round_trip (x : MaterialityOrbitEscapeUp) :
    materialityOrbitEscapeFromEventFlow (materialityOrbitEscapeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk O F I R S T H C P N =>
      change
        some
          (MaterialityOrbitEscapeUp.mk
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist O))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist F))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist I))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist R))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist S))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist T))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist H))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist C))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist P))
            (materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist N))) =
          some (MaterialityOrbitEscapeUp.mk O F I R S T H C P N)
      rw [materialityOrbitEscapeDecode_encode O, materialityOrbitEscapeDecode_encode F,
        materialityOrbitEscapeDecode_encode I, materialityOrbitEscapeDecode_encode R,
        materialityOrbitEscapeDecode_encode S, materialityOrbitEscapeDecode_encode T,
        materialityOrbitEscapeDecode_encode H, materialityOrbitEscapeDecode_encode C,
        materialityOrbitEscapeDecode_encode P, materialityOrbitEscapeDecode_encode N]

private theorem materialityOrbitEscapeToEventFlow_injective
    {x y : MaterialityOrbitEscapeUp} :
    materialityOrbitEscapeToEventFlow x = materialityOrbitEscapeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      materialityOrbitEscapeFromEventFlow (materialityOrbitEscapeToEventFlow x) =
        materialityOrbitEscapeFromEventFlow (materialityOrbitEscapeToEventFlow y) :=
    congrArg materialityOrbitEscapeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (materialityOrbitEscape_round_trip x).symm
      (Eq.trans hread (materialityOrbitEscape_round_trip y)))

private theorem materialityOrbitEscapeFields_faithful :
    ∀ x y : MaterialityOrbitEscapeUp,
      materialityOrbitEscapeFields x = materialityOrbitEscapeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ F₁ I₁ R₁ S₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk O₂ F₂ I₂ R₂ S₂ T₂ H₂ C₂ P₂ N₂ =>
          change
              [O₁, F₁, I₁, R₁, S₁, T₁, H₁, C₁, P₁, N₁] =
                [O₂, F₂, I₂, R₂, S₂, T₂, H₂, C₂, P₂, N₂] at hfields
          injection hfields with hO t1
          injection t1 with hF t2
          injection t2 with hI t3
          injection t3 with hR t4
          injection t4 with hS t5
          injection t5 with hT t6
          injection t6 with hH t7
          injection t7 with hC t8
          injection t8 with hP t9
          injection t9 with hN _
          cases hO
          cases hF
          cases hI
          cases hR
          cases hS
          cases hT
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance materialityOrbitEscapeBHistCarrier : BHistCarrier MaterialityOrbitEscapeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := materialityOrbitEscapeToEventFlow
  fromEventFlow := materialityOrbitEscapeFromEventFlow

instance materialityOrbitEscapeChapterTasteGate :
    ChapterTasteGate MaterialityOrbitEscapeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change materialityOrbitEscapeFromEventFlow (materialityOrbitEscapeToEventFlow x) = some x
    exact materialityOrbitEscape_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (materialityOrbitEscapeToEventFlow_injective heq)

instance materialityOrbitEscapeFieldFaithful :
    FieldFaithful MaterialityOrbitEscapeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := materialityOrbitEscapeFields
  field_faithful := materialityOrbitEscapeFields_faithful

instance materialityOrbitEscapeNontrivial : Nontrivial MaterialityOrbitEscapeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MaterialityOrbitEscapeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MaterialityOrbitEscapeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MaterialityOrbitEscapeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  materialityOrbitEscapeChapterTasteGate

theorem MaterialityOrbitEscapeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      materialityOrbitEscapeDecodeBHist (materialityOrbitEscapeEncodeBHist h) = h) ∧
      (∀ x : MaterialityOrbitEscapeUp,
        materialityOrbitEscapeFromEventFlow (materialityOrbitEscapeToEventFlow x) = some x) ∧
        (∀ x y : MaterialityOrbitEscapeUp,
          materialityOrbitEscapeToEventFlow x = materialityOrbitEscapeToEventFlow y → x = y) ∧
          materialityOrbitEscapeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨materialityOrbitEscapeDecode_encode, materialityOrbitEscape_round_trip,
      (fun _ _ heq => materialityOrbitEscapeToEventFlow_injective heq), rfl⟩

end BEDC.Derived.MaterialityOrbitEscapeUp
