import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TriggerEnergyPartitionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TriggerEnergyPartitionUp : Type where
  | mk (S L E Q K H C P N : BHist) : TriggerEnergyPartitionUp
  deriving DecidableEq

def triggerEnergyPartitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: triggerEnergyPartitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: triggerEnergyPartitionEncodeBHist h

def triggerEnergyPartitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (triggerEnergyPartitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (triggerEnergyPartitionDecodeBHist tail)

private theorem triggerEnergyPartition_decode_encode_bhist :
    ∀ h : BHist,
      triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def triggerEnergyPartitionToEventFlow : TriggerEnergyPartitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TriggerEnergyPartitionUp.mk S L E Q K H C P N =>
      [triggerEnergyPartitionEncodeBHist S,
        triggerEnergyPartitionEncodeBHist L,
        triggerEnergyPartitionEncodeBHist E,
        triggerEnergyPartitionEncodeBHist Q,
        triggerEnergyPartitionEncodeBHist K,
        triggerEnergyPartitionEncodeBHist H,
        triggerEnergyPartitionEncodeBHist C,
        triggerEnergyPartitionEncodeBHist P,
        triggerEnergyPartitionEncodeBHist N]

private def triggerEnergyPartitionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      triggerEnergyPartitionEventAtDefault index rest

def triggerEnergyPartitionFromEventFlow
    (ef : EventFlow) : Option TriggerEnergyPartitionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TriggerEnergyPartitionUp.mk
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 0 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 1 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 2 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 3 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 4 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 5 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 6 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 7 ef))
      (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEventAtDefault 8 ef)))

private theorem triggerEnergyPartition_round_trip :
    ∀ x : TriggerEnergyPartitionUp,
      triggerEnergyPartitionFromEventFlow (triggerEnergyPartitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S L E Q K H C P N =>
      change
        some
          (TriggerEnergyPartitionUp.mk
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist S))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist L))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist E))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist Q))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist K))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist H))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist C))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist P))
            (triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist N))) =
          some (TriggerEnergyPartitionUp.mk S L E Q K H C P N)
      rw [triggerEnergyPartition_decode_encode_bhist S,
        triggerEnergyPartition_decode_encode_bhist L,
        triggerEnergyPartition_decode_encode_bhist E,
        triggerEnergyPartition_decode_encode_bhist Q,
        triggerEnergyPartition_decode_encode_bhist K,
        triggerEnergyPartition_decode_encode_bhist H,
        triggerEnergyPartition_decode_encode_bhist C,
        triggerEnergyPartition_decode_encode_bhist P,
        triggerEnergyPartition_decode_encode_bhist N]

private theorem triggerEnergyPartitionToEventFlow_injective
    {x y : TriggerEnergyPartitionUp} :
    triggerEnergyPartitionToEventFlow x = triggerEnergyPartitionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      triggerEnergyPartitionFromEventFlow (triggerEnergyPartitionToEventFlow x) =
        triggerEnergyPartitionFromEventFlow (triggerEnergyPartitionToEventFlow y) :=
    congrArg triggerEnergyPartitionFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (triggerEnergyPartition_round_trip x).symm
        (Eq.trans hread (triggerEnergyPartition_round_trip y)))

private def triggerEnergyPartitionFields : TriggerEnergyPartitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TriggerEnergyPartitionUp.mk S L E Q K H C P N => [S, L, E, Q, K, H, C, P, N]

private theorem triggerEnergyPartition_fields_faithful :
    ∀ x y : TriggerEnergyPartitionUp,
      triggerEnergyPartitionFields x = triggerEnergyPartitionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ L₁ E₁ Q₁ K₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ L₂ E₂ Q₂ K₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance triggerEnergyPartitionBHistCarrier :
    BHistCarrier TriggerEnergyPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := triggerEnergyPartitionToEventFlow
  fromEventFlow := triggerEnergyPartitionFromEventFlow

instance triggerEnergyPartitionChapterTasteGate :
    ChapterTasteGate TriggerEnergyPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change triggerEnergyPartitionFromEventFlow (triggerEnergyPartitionToEventFlow x) = some x
    exact triggerEnergyPartition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (triggerEnergyPartitionToEventFlow_injective heq)

instance triggerEnergyPartitionFieldFaithful :
    FieldFaithful TriggerEnergyPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := triggerEnergyPartitionFields
  field_faithful := triggerEnergyPartition_fields_faithful

instance triggerEnergyPartitionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial TriggerEnergyPartitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TriggerEnergyPartitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TriggerEnergyPartitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hS _ _ _ _ _ _ _ _
        cases hS⟩

theorem TriggerEnergyPartitionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      triggerEnergyPartitionDecodeBHist (triggerEnergyPartitionEncodeBHist h) = h) ∧
      (∀ x : TriggerEnergyPartitionUp,
        triggerEnergyPartitionFromEventFlow (triggerEnergyPartitionToEventFlow x) = some x) ∧
        (∀ x y : TriggerEnergyPartitionUp,
          triggerEnergyPartitionToEventFlow x = triggerEnergyPartitionToEventFlow y -> x = y) ∧
          triggerEnergyPartitionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨triggerEnergyPartition_decode_encode_bhist,
      triggerEnergyPartition_round_trip,
      (fun _ _ heq => triggerEnergyPartitionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.TriggerEnergyPartitionUp
