import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AlternativeCodeReassignmentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AlternativeCodeReassignmentUp : Type where
  | mk (S T D M Q H C P N : BHist) : AlternativeCodeReassignmentUp
  deriving DecidableEq

def alternativeCodeReassignmentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: alternativeCodeReassignmentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: alternativeCodeReassignmentEncodeBHist h

def alternativeCodeReassignmentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (alternativeCodeReassignmentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (alternativeCodeReassignmentDecodeBHist tail)

private theorem AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def alternativeCodeReassignmentFields : AlternativeCodeReassignmentUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AlternativeCodeReassignmentUp.mk S T D M Q H C P N => [S, T, D, M, Q, H, C, P, N]

def alternativeCodeReassignmentToEventFlow : AlternativeCodeReassignmentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (alternativeCodeReassignmentFields x).map alternativeCodeReassignmentEncodeBHist

private def alternativeCodeReassignmentEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => alternativeCodeReassignmentEventAt index rest

def alternativeCodeReassignmentFromEventFlow (ef : EventFlow) :
    Option AlternativeCodeReassignmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AlternativeCodeReassignmentUp.mk
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 0 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 1 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 2 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 3 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 4 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 5 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 6 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 7 ef))
      (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEventAt 8 ef)))

private theorem AlternativeCodeReassignmentTasteGate_single_carrier_alignment_round_trip
    (x : AlternativeCodeReassignmentUp) :
    alternativeCodeReassignmentFromEventFlow (alternativeCodeReassignmentToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T D M Q H C P N =>
      change
        some
          (AlternativeCodeReassignmentUp.mk
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist S))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist T))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist D))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist M))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist Q))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist H))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist C))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist P))
            (alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist N))) =
          some (AlternativeCodeReassignmentUp.mk S T D M Q H C P N)
      rw [AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode S,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode T,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode D,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode M,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode Q,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode H,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode C,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode P,
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode N]

private theorem AlternativeCodeReassignmentTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AlternativeCodeReassignmentUp} :
    alternativeCodeReassignmentToEventFlow x = alternativeCodeReassignmentToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      alternativeCodeReassignmentFromEventFlow (alternativeCodeReassignmentToEventFlow x) =
        alternativeCodeReassignmentFromEventFlow (alternativeCodeReassignmentToEventFlow y) :=
    congrArg alternativeCodeReassignmentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AlternativeCodeReassignmentTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AlternativeCodeReassignmentTasteGate_single_carrier_alignment_round_trip y)))

private theorem AlternativeCodeReassignmentTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AlternativeCodeReassignmentUp,
      alternativeCodeReassignmentFields x = alternativeCodeReassignmentFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ T₁ D₁ M₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ T₂ D₂ M₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance alternativeCodeReassignmentBHistCarrier :
    BHistCarrier AlternativeCodeReassignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := alternativeCodeReassignmentToEventFlow
  fromEventFlow := alternativeCodeReassignmentFromEventFlow

instance alternativeCodeReassignmentChapterTasteGate :
    ChapterTasteGate AlternativeCodeReassignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change alternativeCodeReassignmentFromEventFlow (alternativeCodeReassignmentToEventFlow x) =
      some x
    exact AlternativeCodeReassignmentTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AlternativeCodeReassignmentTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance alternativeCodeReassignmentFieldFaithful :
    FieldFaithful AlternativeCodeReassignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := alternativeCodeReassignmentFields
  field_faithful := AlternativeCodeReassignmentTasteGate_single_carrier_alignment_fields_faithful

instance alternativeCodeReassignmentNontrivial : Nontrivial AlternativeCodeReassignmentUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AlternativeCodeReassignmentUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AlternativeCodeReassignmentUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def AlternativeCodeReassignmentTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate AlternativeCodeReassignmentUp :=
  -- BEDC touchpoint anchor: BHist BMark
  alternativeCodeReassignmentChapterTasteGate

theorem AlternativeCodeReassignmentTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      alternativeCodeReassignmentDecodeBHist (alternativeCodeReassignmentEncodeBHist h) = h) ∧
      (∀ x : AlternativeCodeReassignmentUp,
        alternativeCodeReassignmentFromEventFlow (alternativeCodeReassignmentToEventFlow x) =
          some x) ∧
        (∀ x y : AlternativeCodeReassignmentUp,
          alternativeCodeReassignmentToEventFlow x = alternativeCodeReassignmentToEventFlow y →
            x = y) ∧
          alternativeCodeReassignmentEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨AlternativeCodeReassignmentTasteGate_single_carrier_alignment_decode_encode,
      AlternativeCodeReassignmentTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AlternativeCodeReassignmentTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AlternativeCodeReassignmentUp
