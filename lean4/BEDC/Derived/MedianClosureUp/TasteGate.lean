import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MedianClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MedianClosureUp : Type where
  | mk (S M I F X H C P N : BHist) : MedianClosureUp
  deriving DecidableEq

def medianClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: medianClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: medianClosureEncodeBHist h

def medianClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (medianClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (medianClosureDecodeBHist tail)

private theorem MedianClosureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, medianClosureDecodeBHist (medianClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def medianClosureFields : MedianClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MedianClosureUp.mk S M I F X H C P N => [S, M, I, F, X, H, C, P, N]

def medianClosureToEventFlow : MedianClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (medianClosureFields x).map medianClosureEncodeBHist

private def MedianClosureTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      MedianClosureTasteGate_single_carrier_alignment_eventAtDefault index rest

def medianClosureFromEventFlow (ef : EventFlow) : Option MedianClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MedianClosureUp.mk
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (medianClosureDecodeBHist
        (MedianClosureTasteGate_single_carrier_alignment_eventAtDefault 8 ef)))

private theorem MedianClosureTasteGate_single_carrier_alignment_round_trip
    (x : MedianClosureUp) :
    medianClosureFromEventFlow (medianClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M I F X H C P N =>
      change
        some
          (MedianClosureUp.mk
            (medianClosureDecodeBHist (medianClosureEncodeBHist S))
            (medianClosureDecodeBHist (medianClosureEncodeBHist M))
            (medianClosureDecodeBHist (medianClosureEncodeBHist I))
            (medianClosureDecodeBHist (medianClosureEncodeBHist F))
            (medianClosureDecodeBHist (medianClosureEncodeBHist X))
            (medianClosureDecodeBHist (medianClosureEncodeBHist H))
            (medianClosureDecodeBHist (medianClosureEncodeBHist C))
            (medianClosureDecodeBHist (medianClosureEncodeBHist P))
            (medianClosureDecodeBHist (medianClosureEncodeBHist N))) =
          some (MedianClosureUp.mk S M I F X H C P N)
      rw [MedianClosureTasteGate_single_carrier_alignment_decode_encode S,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode M,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode I,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode F,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode X,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode H,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode C,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode P,
        MedianClosureTasteGate_single_carrier_alignment_decode_encode N]

private theorem MedianClosureTasteGate_single_carrier_alignment_injective
    {x y : MedianClosureUp} :
    medianClosureToEventFlow x = medianClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      medianClosureFromEventFlow (medianClosureToEventFlow x) =
        medianClosureFromEventFlow (medianClosureToEventFlow y) :=
    congrArg medianClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MedianClosureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MedianClosureTasteGate_single_carrier_alignment_round_trip y)))

private theorem MedianClosureTasteGate_single_carrier_alignment_fields :
    ∀ x y : MedianClosureUp,
      medianClosureFields x = medianClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ M₁ I₁ F₁ X₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ M₂ I₂ F₂ X₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance medianClosureBHistCarrier : BHistCarrier MedianClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := medianClosureToEventFlow
  fromEventFlow := medianClosureFromEventFlow

instance medianClosureChapterTasteGate : ChapterTasteGate MedianClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change medianClosureFromEventFlow (medianClosureToEventFlow x) = some x
    exact MedianClosureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MedianClosureTasteGate_single_carrier_alignment_injective heq)

instance medianClosureFieldFaithful : FieldFaithful MedianClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := medianClosureFields
  field_faithful := MedianClosureTasteGate_single_carrier_alignment_fields

instance medianClosureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MedianClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MedianClosureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MedianClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def MedianClosureTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate MedianClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  medianClosureChapterTasteGate

theorem MedianClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist, medianClosureDecodeBHist (medianClosureEncodeBHist h) = h) ∧
      Nonempty (ChapterTasteGate MedianClosureUp) ∧
        Nonempty (FieldFaithful MedianClosureUp) ∧
          Nonempty (BEDC.Meta.TasteGate.Nontrivial MedianClosureUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MedianClosureTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact ⟨medianClosureChapterTasteGate⟩
    · constructor
      · exact ⟨medianClosureFieldFaithful⟩
      · exact ⟨medianClosureNontrivial⟩

end BEDC.Derived.MedianClosureUp
