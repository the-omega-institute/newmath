import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactMetricCompletionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactMetricCompletionUp : Type where
  | mk
      (totallyBoundedCompletion completeUniformSpace totallyBoundedLedger compactExport
        realSeal transport replay provenance localNameCert : BHist) :
      CompactMetricCompletionUp
  deriving DecidableEq

def compactMetricCompletionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactMetricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactMetricCompletionEncodeBHist h

def compactMetricCompletionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactMetricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactMetricCompletionDecodeBHist tail)

private theorem compactMetricCompletion_decode_encode_bhist :
    forall h : BHist,
      compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactMetricCompletionFields : CompactMetricCompletionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactMetricCompletionUp.mk T U B K E H C P N => [T, U, B, K, E, H, C, P, N]

def compactMetricCompletionToEventFlow : CompactMetricCompletionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactMetricCompletionFields x).map compactMetricCompletionEncodeBHist

private def compactMetricCompletionEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactMetricCompletionEventAtDefault index rest

private def compactMetricCompletionExactLength : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => true
  | Nat.zero, _event :: _rest => false
  | Nat.succ _index, [] => false
  | Nat.succ index, _event :: rest => compactMetricCompletionExactLength index rest

def compactMetricCompletionFromEventFlow (ef : EventFlow) : Option CompactMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match compactMetricCompletionExactLength 9 ef with
  | true =>
      some
        (CompactMetricCompletionUp.mk
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 0 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 1 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 2 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 3 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 4 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 5 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 6 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 7 ef))
          (compactMetricCompletionDecodeBHist (compactMetricCompletionEventAtDefault 8 ef)))
  | false => none

private theorem compactMetricCompletion_round_trip :
    forall x : CompactMetricCompletionUp,
      compactMetricCompletionFromEventFlow (compactMetricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T U B K E H C P N =>
      change
        some
          (CompactMetricCompletionUp.mk
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist T))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist U))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist B))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist K))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist E))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist H))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist C))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist P))
            (compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist N))) =
          some (CompactMetricCompletionUp.mk T U B K E H C P N)
      rw [compactMetricCompletion_decode_encode_bhist T,
        compactMetricCompletion_decode_encode_bhist U,
        compactMetricCompletion_decode_encode_bhist B,
        compactMetricCompletion_decode_encode_bhist K,
        compactMetricCompletion_decode_encode_bhist E,
        compactMetricCompletion_decode_encode_bhist H,
        compactMetricCompletion_decode_encode_bhist C,
        compactMetricCompletion_decode_encode_bhist P,
        compactMetricCompletion_decode_encode_bhist N]

private theorem compactMetricCompletionToEventFlow_injective {x y : CompactMetricCompletionUp} :
    compactMetricCompletionToEventFlow x = compactMetricCompletionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactMetricCompletionFromEventFlow (compactMetricCompletionToEventFlow x) =
        compactMetricCompletionFromEventFlow (compactMetricCompletionToEventFlow y) :=
    congrArg compactMetricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactMetricCompletion_round_trip x).symm
      (Eq.trans hread (compactMetricCompletion_round_trip y)))

private theorem compactMetricCompletion_field_faithful :
    forall x y : CompactMetricCompletionUp,
      compactMetricCompletionFields x = compactMetricCompletionFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 U1 B1 K1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk T2 U2 B2 K2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactMetricCompletionBHistCarrier : BHistCarrier CompactMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactMetricCompletionToEventFlow
  fromEventFlow := compactMetricCompletionFromEventFlow

instance compactMetricCompletionChapterTasteGate :
    ChapterTasteGate CompactMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactMetricCompletionFromEventFlow (compactMetricCompletionToEventFlow x) = some x
    exact compactMetricCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactMetricCompletionToEventFlow_injective heq)

instance compactMetricCompletionFieldFaithful : FieldFaithful CompactMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactMetricCompletionFields
  field_faithful := compactMetricCompletion_field_faithful

instance compactMetricCompletionNontrivial : Nontrivial CompactMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactMetricCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactMetricCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompactMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactMetricCompletionChapterTasteGate

theorem CompactMetricCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactMetricCompletionUp) ∧
      Nonempty (FieldFaithful CompactMetricCompletionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactMetricCompletionUp) ∧
          (∀ h : BHist,
            compactMetricCompletionDecodeBHist (compactMetricCompletionEncodeBHist h) = h) ∧
            (∀ x : CompactMetricCompletionUp,
              compactMetricCompletionFromEventFlow (compactMetricCompletionToEventFlow x) =
                some x) ∧
              (∀ x y : CompactMetricCompletionUp,
                compactMetricCompletionToEventFlow x = compactMetricCompletionToEventFlow y →
                  x = y) ∧
                compactMetricCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨compactMetricCompletionChapterTasteGate⟩,
      ⟨compactMetricCompletionFieldFaithful⟩,
      ⟨compactMetricCompletionNontrivial⟩,
      compactMetricCompletion_decode_encode_bhist,
      compactMetricCompletion_round_trip,
      (fun _ _ heq => compactMetricCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactMetricCompletionUp.TasteGate
