import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FourFaceExitClassifierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FourFaceExitClassifierUp : Type where
  | mk : (S D R E H C P N : BHist) → FourFaceExitClassifierUp
  deriving DecidableEq

def fourFaceExitClassifierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fourFaceExitClassifierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fourFaceExitClassifierEncodeBHist h

def fourFaceExitClassifierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fourFaceExitClassifierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fourFaceExitClassifierDecodeBHist tail)

private theorem FourFaceExitClassifierTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def fourFaceExitClassifierToEventFlow : FourFaceExitClassifierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FourFaceExitClassifierUp.mk S D R E H C P N =>
      [[BMark.b0, BMark.b1, BMark.b0],
        fourFaceExitClassifierEncodeBHist S,
        fourFaceExitClassifierEncodeBHist D,
        fourFaceExitClassifierEncodeBHist R,
        fourFaceExitClassifierEncodeBHist E,
        fourFaceExitClassifierEncodeBHist H,
        fourFaceExitClassifierEncodeBHist C,
        fourFaceExitClassifierEncodeBHist P,
        fourFaceExitClassifierEncodeBHist N]

private def fourFaceExitClassifierEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => fourFaceExitClassifierEventAtDefault index rest

def fourFaceExitClassifierFromEventFlow :
    EventFlow → Option FourFaceExitClassifierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FourFaceExitClassifierUp.mk
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 1 ef))
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 2 ef))
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 3 ef))
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 4 ef))
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 5 ef))
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 6 ef))
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 7 ef))
        (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEventAtDefault 8 ef)))

private def fourFaceExitClassifierFields : FourFaceExitClassifierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FourFaceExitClassifierUp.mk S D R E H C P N => [S, D, R, E, H, C, P, N]

private theorem FourFaceExitClassifierTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FourFaceExitClassifierUp,
      fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D R E H C P N =>
      change
        some
          (FourFaceExitClassifierUp.mk
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist S))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist D))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist R))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist E))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist H))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist C))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist P))
            (fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist N))) =
          some (FourFaceExitClassifierUp.mk S D R E H C P N)
      rw [FourFaceExitClassifierTasteGate_single_carrier_alignment_decode S,
        FourFaceExitClassifierTasteGate_single_carrier_alignment_decode D,
        FourFaceExitClassifierTasteGate_single_carrier_alignment_decode R,
        FourFaceExitClassifierTasteGate_single_carrier_alignment_decode E,
        FourFaceExitClassifierTasteGate_single_carrier_alignment_decode H,
        FourFaceExitClassifierTasteGate_single_carrier_alignment_decode C,
        FourFaceExitClassifierTasteGate_single_carrier_alignment_decode P,
        FourFaceExitClassifierTasteGate_single_carrier_alignment_decode N]

private theorem fourFaceExitClassifierToEventFlow_injective
    {x y : FourFaceExitClassifierUp} :
    fourFaceExitClassifierToEventFlow x = fourFaceExitClassifierToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) =
        fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow y) :=
    congrArg fourFaceExitClassifierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FourFaceExitClassifierTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FourFaceExitClassifierTasteGate_single_carrier_alignment_round_trip y)))

private theorem fourFaceExitClassifier_field_faithful :
    ∀ x y : FourFaceExitClassifierUp,
      fourFaceExitClassifierFields x = fourFaceExitClassifierFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          injection h with hS t1
          injection t1 with hD t2
          injection t2 with hR t3
          injection t3 with hE t4
          injection t4 with hH t5
          injection t5 with hC t6
          injection t6 with hP t7
          injection t7 with hN _
          cases hS
          cases hD
          cases hR
          cases hE
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance fourFaceExitClassifierBHistCarrier : BHistCarrier FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fourFaceExitClassifierToEventFlow
  fromEventFlow := fourFaceExitClassifierFromEventFlow

instance fourFaceExitClassifierChapterTasteGate :
    ChapterTasteGate FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) = some x
    exact FourFaceExitClassifierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fourFaceExitClassifierToEventFlow_injective heq)

instance fourFaceExitClassifierFieldFaithful : FieldFaithful FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fourFaceExitClassifierFields
  field_faithful := fourFaceExitClassifier_field_faithful

instance fourFaceExitClassifierNontrivial : Nontrivial FourFaceExitClassifierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FourFaceExitClassifierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FourFaceExitClassifierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem FourFaceExitClassifierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      fourFaceExitClassifierDecodeBHist (fourFaceExitClassifierEncodeBHist h) = h) ∧
      (∀ x : FourFaceExitClassifierUp,
        fourFaceExitClassifierFromEventFlow (fourFaceExitClassifierToEventFlow x) =
          some x) ∧
        (∀ x y : FourFaceExitClassifierUp,
          fourFaceExitClassifierToEventFlow x = fourFaceExitClassifierToEventFlow y →
            x = y) ∧
          fourFaceExitClassifierEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact FourFaceExitClassifierTasteGate_single_carrier_alignment_decode
  · constructor
    · exact FourFaceExitClassifierTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact fourFaceExitClassifierToEventFlow_injective heq
      · rfl

end BEDC.Derived.FourFaceExitClassifierUp
