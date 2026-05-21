import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HardProblemClosureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HardProblemClosureUp : Type where
  | mk :
      (generatedRecords localChoices compression witnessedRelations invariants boundary transport
        replay provenance name : BHist) →
      HardProblemClosureUp
  deriving DecidableEq

def hardProblemClosureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hardProblemClosureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hardProblemClosureEncodeBHist h

def hardProblemClosureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hardProblemClosureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hardProblemClosureDecodeBHist tail)

private theorem hardProblemClosure_decode_encode_bhist :
    ∀ h : BHist, hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hardProblemClosureFields : HardProblemClosureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HardProblemClosureUp.mk generatedRecords localChoices compression witnessedRelations
      invariants boundary transport replay provenance name =>
      [generatedRecords, localChoices, compression, witnessedRelations, invariants, boundary,
        transport, replay, provenance, name]

def hardProblemClosureToEventFlow : HardProblemClosureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hardProblemClosureFields x).map hardProblemClosureEncodeBHist

private def hardProblemClosureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hardProblemClosureEventAtDefault index rest

def hardProblemClosureFromEventFlow (ef : EventFlow) : Option HardProblemClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HardProblemClosureUp.mk
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 0 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 1 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 2 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 3 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 4 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 5 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 6 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 7 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 8 ef))
      (hardProblemClosureDecodeBHist (hardProblemClosureEventAtDefault 9 ef)))

private theorem hardProblemClosure_round_trip :
    ∀ x : HardProblemClosureUp,
      hardProblemClosureFromEventFlow (hardProblemClosureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generatedRecords localChoices compression witnessedRelations invariants boundary
      transport replay provenance name =>
      change
        some
          (HardProblemClosureUp.mk
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist generatedRecords))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist localChoices))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist compression))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist witnessedRelations))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist invariants))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist boundary))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist transport))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist replay))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist provenance))
            (hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist name))) =
          some
            (HardProblemClosureUp.mk generatedRecords localChoices compression witnessedRelations
              invariants boundary transport replay provenance name)
      rw [hardProblemClosure_decode_encode_bhist generatedRecords,
        hardProblemClosure_decode_encode_bhist localChoices,
        hardProblemClosure_decode_encode_bhist compression,
        hardProblemClosure_decode_encode_bhist witnessedRelations,
        hardProblemClosure_decode_encode_bhist invariants,
        hardProblemClosure_decode_encode_bhist boundary,
        hardProblemClosure_decode_encode_bhist transport,
        hardProblemClosure_decode_encode_bhist replay,
        hardProblemClosure_decode_encode_bhist provenance,
        hardProblemClosure_decode_encode_bhist name]

private theorem hardProblemClosureToEventFlow_injective {x y : HardProblemClosureUp} :
    hardProblemClosureToEventFlow x = hardProblemClosureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hardProblemClosureFromEventFlow (hardProblemClosureToEventFlow x) =
        hardProblemClosureFromEventFlow (hardProblemClosureToEventFlow y) :=
    congrArg hardProblemClosureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hardProblemClosure_round_trip x).symm
      (Eq.trans hread (hardProblemClosure_round_trip y)))

private theorem hardProblemClosure_fields_faithful :
    ∀ x y : HardProblemClosureUp, hardProblemClosureFields x = hardProblemClosureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk r₁ l₁ c₁ w₁ i₁ b₁ h₁ q₁ p₁ n₁ =>
      cases y with
      | mk r₂ l₂ c₂ w₂ i₂ b₂ h₂ q₂ p₂ n₂ =>
          cases hfields
          rfl

instance hardProblemClosureBHistCarrier : BHistCarrier HardProblemClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hardProblemClosureToEventFlow
  fromEventFlow := hardProblemClosureFromEventFlow

instance hardProblemClosureChapterTasteGate : ChapterTasteGate HardProblemClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hardProblemClosureFromEventFlow (hardProblemClosureToEventFlow x) = some x
    exact hardProblemClosure_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hardProblemClosureToEventFlow_injective heq)

instance hardProblemClosureFieldFaithful : FieldFaithful HardProblemClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hardProblemClosureFields
  field_faithful := hardProblemClosure_fields_faithful

instance hardProblemClosureNontrivial : Nontrivial HardProblemClosureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HardProblemClosureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HardProblemClosureUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HardProblemClosureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hardProblemClosureChapterTasteGate

theorem HardProblemClosureTasteGate_single_carrier_alignment :
    (∀ h : BHist, hardProblemClosureDecodeBHist (hardProblemClosureEncodeBHist h) = h) ∧
      (∀ x : HardProblemClosureUp,
        hardProblemClosureFromEventFlow (hardProblemClosureToEventFlow x) = some x) ∧
        (∀ x y : HardProblemClosureUp,
          hardProblemClosureToEventFlow x = hardProblemClosureToEventFlow y → x = y) ∧
          hardProblemClosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨hardProblemClosure_decode_encode_bhist,
      hardProblemClosure_round_trip,
      (fun _ _ heq => hardProblemClosureToEventFlow_injective heq),
      rfl⟩

theorem HardProblemClosure_boundary_exposure (x : HardProblemClosureUp) :
    ∃ R L C W I B H Q P N : BHist,
      x = HardProblemClosureUp.mk R L C W I B H Q P N ∧
        hardProblemClosureFields x = [R, L, C, W, I, B, H, Q, P, N] ∧
          hsame B B ∧
            hsame H H ∧
              hardProblemClosureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  cases x with
  | mk R L C W I B H Q P N =>
      exact
        ⟨R, L, C, W, I, B, H, Q, P, N, rfl, rfl, hsame_refl B, hsame_refl H, rfl⟩

end BEDC.Derived.HardProblemClosureUp
