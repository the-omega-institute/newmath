import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MedianClosureSpectrumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MedianClosureSpectrumUp : Type where
  | mk (Q W D S L E R H C P N : BHist) : MedianClosureSpectrumUp
  deriving DecidableEq

def medianClosureSpectrumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: medianClosureSpectrumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: medianClosureSpectrumEncodeBHist h

def medianClosureSpectrumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (medianClosureSpectrumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (medianClosureSpectrumDecodeBHist tail)

private theorem MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def medianClosureSpectrumFields : MedianClosureSpectrumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MedianClosureSpectrumUp.mk Q W D S L E R H C P N =>
      [Q, W, D, S, L, E, R, H, C, P, N]

def medianClosureSpectrumToEventFlow : MedianClosureSpectrumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (medianClosureSpectrumFields x).map medianClosureSpectrumEncodeBHist

private def medianClosureSpectrumEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => medianClosureSpectrumEventAtDefault index rest

def medianClosureSpectrumFromEventFlow (ef : EventFlow) :
    Option MedianClosureSpectrumUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MedianClosureSpectrumUp.mk
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 0 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 1 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 2 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 3 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 4 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 5 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 6 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 7 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 8 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 9 ef))
      (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEventAtDefault 10 ef)))

private theorem MedianClosureSpectrumTasteGate_single_carrier_alignment_round_trip
    (x : MedianClosureSpectrumUp) :
    medianClosureSpectrumFromEventFlow (medianClosureSpectrumToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q W D S L E R H C P N =>
      change
        some
          (MedianClosureSpectrumUp.mk
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist Q))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist W))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist D))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist S))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist L))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist E))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist R))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist H))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist C))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist P))
            (medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist N))) =
          some (MedianClosureSpectrumUp.mk Q W D S L E R H C P N)
      rw [MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode Q,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode W,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode D,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode S,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode L,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode E,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode R,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode H,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode C,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode P,
        MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode N]

private theorem MedianClosureSpectrumTasteGate_single_carrier_alignment_injective
    {x y : MedianClosureSpectrumUp} :
    medianClosureSpectrumToEventFlow x = medianClosureSpectrumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      medianClosureSpectrumFromEventFlow (medianClosureSpectrumToEventFlow x) =
        medianClosureSpectrumFromEventFlow (medianClosureSpectrumToEventFlow y) :=
    congrArg medianClosureSpectrumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MedianClosureSpectrumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MedianClosureSpectrumTasteGate_single_carrier_alignment_round_trip y)))

private theorem MedianClosureSpectrumTasteGate_single_carrier_alignment_fields :
    ∀ x y : MedianClosureSpectrumUp,
      medianClosureSpectrumFields x = medianClosureSpectrumFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q₁ W₁ D₁ S₁ L₁ E₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk Q₂ W₂ D₂ S₂ L₂ E₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance medianClosureSpectrumBHistCarrier : BHistCarrier MedianClosureSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := medianClosureSpectrumToEventFlow
  fromEventFlow := medianClosureSpectrumFromEventFlow

instance medianClosureSpectrumChapterTasteGate :
    ChapterTasteGate MedianClosureSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change medianClosureSpectrumFromEventFlow (medianClosureSpectrumToEventFlow x) = some x
    exact MedianClosureSpectrumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MedianClosureSpectrumTasteGate_single_carrier_alignment_injective heq)

instance medianClosureSpectrumFieldFaithful : FieldFaithful MedianClosureSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := medianClosureSpectrumFields
  field_faithful := MedianClosureSpectrumTasteGate_single_carrier_alignment_fields

instance medianClosureSpectrumNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MedianClosureSpectrumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MedianClosureSpectrumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MedianClosureSpectrumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MedianClosureSpectrumTasteGate_single_carrier_alignment :
    (∀ h : BHist, medianClosureSpectrumDecodeBHist (medianClosureSpectrumEncodeBHist h) = h) ∧
      (∀ x : MedianClosureSpectrumUp,
        medianClosureSpectrumFromEventFlow (medianClosureSpectrumToEventFlow x) = some x) ∧
        (∀ x y : MedianClosureSpectrumUp,
          medianClosureSpectrumToEventFlow x = medianClosureSpectrumToEventFlow y → x = y) ∧
          medianClosureSpectrumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MedianClosureSpectrumTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact MedianClosureSpectrumTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact MedianClosureSpectrumTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.MedianClosureSpectrumUp
