import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalSubsequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalSubsequenceUp : Type where
  | mk (S W J R Q E H C P N : BHist) : DiagonalSubsequenceUp
  deriving DecidableEq

def diagonalSubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalSubsequenceEncodeBHist h

def diagonalSubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalSubsequenceDecodeBHist tail)

private theorem diagonalSubsequenceDecode_encode :
    ∀ h : BHist, diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diagonalSubsequenceFields : DiagonalSubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalSubsequenceUp.mk S W J R Q E H C P N => [S, W, J, R, Q, E, H, C, P, N]

def diagonalSubsequenceToEventFlow : DiagonalSubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map diagonalSubsequenceEncodeBHist (diagonalSubsequenceFields x)

private def diagonalSubsequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diagonalSubsequenceRawAt index rest

def diagonalSubsequenceFromEventFlow (flow : EventFlow) : Option DiagonalSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DiagonalSubsequenceUp.mk
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 0 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 1 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 2 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 3 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 4 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 5 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 6 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 7 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 8 flow))
      (diagonalSubsequenceDecodeBHist (diagonalSubsequenceRawAt 9 flow)))

private theorem diagonalSubsequence_round_trip :
    ∀ x : DiagonalSubsequenceUp,
      diagonalSubsequenceFromEventFlow (diagonalSubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W J R Q E H C P N =>
      change
        some
          (DiagonalSubsequenceUp.mk
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist S))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist W))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist J))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist R))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist Q))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist E))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist H))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist C))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist P))
            (diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist N))) =
          some (DiagonalSubsequenceUp.mk S W J R Q E H C P N)
      rw [diagonalSubsequenceDecode_encode S, diagonalSubsequenceDecode_encode W,
        diagonalSubsequenceDecode_encode J, diagonalSubsequenceDecode_encode R,
        diagonalSubsequenceDecode_encode Q, diagonalSubsequenceDecode_encode E,
        diagonalSubsequenceDecode_encode H, diagonalSubsequenceDecode_encode C,
        diagonalSubsequenceDecode_encode P, diagonalSubsequenceDecode_encode N]

private theorem diagonalSubsequenceToEventFlow_injective {x y : DiagonalSubsequenceUp} :
    diagonalSubsequenceToEventFlow x = diagonalSubsequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalSubsequenceFromEventFlow (diagonalSubsequenceToEventFlow x) =
        diagonalSubsequenceFromEventFlow (diagonalSubsequenceToEventFlow y) :=
    congrArg diagonalSubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalSubsequence_round_trip x).symm
      (Eq.trans hread (diagonalSubsequence_round_trip y)))

private theorem diagonalSubsequence_fields_faithful :
    ∀ x y : DiagonalSubsequenceUp, diagonalSubsequenceFields x = diagonalSubsequenceFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ W₁ J₁ R₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ W₂ J₂ R₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          simp only [diagonalSubsequenceFields] at h
          cases h
          rfl

instance diagonalSubsequenceBHistCarrier : BHistCarrier DiagonalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalSubsequenceToEventFlow
  fromEventFlow := diagonalSubsequenceFromEventFlow

instance diagonalSubsequenceChapterTasteGate : ChapterTasteGate DiagonalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalSubsequenceFromEventFlow (diagonalSubsequenceToEventFlow x) = some x
    exact diagonalSubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalSubsequenceToEventFlow_injective heq)

instance diagonalSubsequenceFieldFaithful : FieldFaithful DiagonalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diagonalSubsequenceFields
  field_faithful := diagonalSubsequence_fields_faithful

instance diagonalSubsequenceNontrivial : Nontrivial DiagonalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalSubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DiagonalSubsequenceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DiagonalSubsequenceUp) ∧
      Nonempty (FieldFaithful DiagonalSubsequenceUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial DiagonalSubsequenceUp) ∧
          (∀ h : BHist, diagonalSubsequenceDecodeBHist (diagonalSubsequenceEncodeBHist h) = h) ∧
            (∀ x : DiagonalSubsequenceUp,
              diagonalSubsequenceFromEventFlow (diagonalSubsequenceToEventFlow x) = some x) ∧
              (∀ x y : DiagonalSubsequenceUp,
                diagonalSubsequenceToEventFlow x = diagonalSubsequenceToEventFlow y → x = y) ∧
                diagonalSubsequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨diagonalSubsequenceChapterTasteGate⟩,
      ⟨diagonalSubsequenceFieldFaithful⟩,
      ⟨diagonalSubsequenceNontrivial⟩,
      diagonalSubsequenceDecode_encode,
      diagonalSubsequence_round_trip,
      by
        intro x y heq
        exact diagonalSubsequenceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DiagonalSubsequenceUp.TasteGate
