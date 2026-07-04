import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteTriggerFlipGraphUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteTriggerFlipGraphUp : Type where
  | mk
      (quotientTriggers liftFibers edgeRows edgeBudget transport replay provenance
        localName : BHist) :
      FiniteTriggerFlipGraphUp

def finiteTriggerFlipGraphEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteTriggerFlipGraphEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteTriggerFlipGraphEncodeBHist h

def finiteTriggerFlipGraphDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteTriggerFlipGraphDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteTriggerFlipGraphDecodeBHist tail)

private theorem FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteTriggerFlipGraphFields : FiniteTriggerFlipGraphUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteTriggerFlipGraphUp.mk quotientTriggers liftFibers edgeRows edgeBudget transport
      replay provenance localName =>
      [quotientTriggers, liftFibers, edgeRows, edgeBudget, transport, replay, provenance,
        localName]

def finiteTriggerFlipGraphToEventFlow : FiniteTriggerFlipGraphUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteTriggerFlipGraphFields x).map finiteTriggerFlipGraphEncodeBHist

private def finiteTriggerFlipGraphEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteTriggerFlipGraphEventAtDefault index rest

def finiteTriggerFlipGraphFromEventFlow (ef : EventFlow) : Option FiniteTriggerFlipGraphUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteTriggerFlipGraphUp.mk
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 0 ef))
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 1 ef))
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 2 ef))
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 3 ef))
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 4 ef))
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 5 ef))
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 6 ef))
      (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEventAtDefault 7 ef)))

private theorem FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_round_trip
    (x : FiniteTriggerFlipGraphUp) :
    finiteTriggerFlipGraphFromEventFlow (finiteTriggerFlipGraphToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk quotientTriggers liftFibers edgeRows edgeBudget transport replay provenance
      localName =>
      change
        some
          (FiniteTriggerFlipGraphUp.mk
            (finiteTriggerFlipGraphDecodeBHist
              (finiteTriggerFlipGraphEncodeBHist quotientTriggers))
            (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist liftFibers))
            (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist edgeRows))
            (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist edgeBudget))
            (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist transport))
            (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist replay))
            (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist provenance))
            (finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist localName))) =
          some
            (FiniteTriggerFlipGraphUp.mk quotientTriggers liftFibers edgeRows edgeBudget
              transport replay provenance localName)
      rw [FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode quotientTriggers,
        FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode liftFibers,
        FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode edgeRows,
        FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode edgeBudget,
        FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode transport,
        FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode replay,
        FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode provenance,
        FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode localName]

private theorem FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_injective
    {x y : FiniteTriggerFlipGraphUp} :
    finiteTriggerFlipGraphToEventFlow x = finiteTriggerFlipGraphToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteTriggerFlipGraphFromEventFlow (finiteTriggerFlipGraphToEventFlow x) =
        finiteTriggerFlipGraphFromEventFlow (finiteTriggerFlipGraphToEventFlow y) :=
    congrArg finiteTriggerFlipGraphFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_round_trip y)))

private theorem FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_fields :
    ∀ x y : FiniteTriggerFlipGraphUp,
      finiteTriggerFlipGraphFields x = finiteTriggerFlipGraphFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk quotientTriggers₁ liftFibers₁ edgeRows₁ edgeBudget₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk quotientTriggers₂ liftFibers₂ edgeRows₂ edgeBudget₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance finiteTriggerFlipGraphBHistCarrier : BHistCarrier FiniteTriggerFlipGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteTriggerFlipGraphToEventFlow
  fromEventFlow := finiteTriggerFlipGraphFromEventFlow

instance finiteTriggerFlipGraphChapterTasteGate :
    ChapterTasteGate FiniteTriggerFlipGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteTriggerFlipGraphFromEventFlow (finiteTriggerFlipGraphToEventFlow x) = some x
    exact FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_injective heq)

instance finiteTriggerFlipGraphFieldFaithful : FieldFaithful FiniteTriggerFlipGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteTriggerFlipGraphFields
  field_faithful := FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_fields

instance finiteTriggerFlipGraphNontrivial :
    BEDC.Meta.TasteGate.Nontrivial FiniteTriggerFlipGraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteTriggerFlipGraphUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteTriggerFlipGraphUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate FiniteTriggerFlipGraphUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteTriggerFlipGraphChapterTasteGate

theorem FiniteTriggerFlipGraphTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteTriggerFlipGraphDecodeBHist (finiteTriggerFlipGraphEncodeBHist h) = h) ∧
      (∀ x : FiniteTriggerFlipGraphUp,
        finiteTriggerFlipGraphFromEventFlow (finiteTriggerFlipGraphToEventFlow x) = some x) ∧
        (∀ x y : FiniteTriggerFlipGraphUp,
          finiteTriggerFlipGraphToEventFlow x = finiteTriggerFlipGraphToEventFlow y →
            x = y) ∧
          Nonempty (FieldFaithful FiniteTriggerFlipGraphUp) ∧
            Nonempty (Nontrivial FiniteTriggerFlipGraphUp) ∧
              finiteTriggerFlipGraphEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FiniteTriggerFlipGraphTasteGate_single_carrier_alignment_injective heq
      · constructor
        · exact ⟨finiteTriggerFlipGraphFieldFaithful⟩
        · constructor
          · exact ⟨finiteTriggerFlipGraphNontrivial⟩
          · rfl

end BEDC.Derived.FiniteTriggerFlipGraphUp
