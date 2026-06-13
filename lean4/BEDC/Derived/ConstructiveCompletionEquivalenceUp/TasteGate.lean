import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveCompletionEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveCompletionEquivalenceUp : Type where
  | mk (C B U M S D R A H K P N : BHist) : ConstructiveCompletionEquivalenceUp
  deriving DecidableEq

def constructiveCompletionEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveCompletionEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveCompletionEquivalenceEncodeBHist h

def constructiveCompletionEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveCompletionEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveCompletionEquivalenceDecodeBHist tail)

theorem ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveCompletionEquivalenceFields :
    ConstructiveCompletionEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveCompletionEquivalenceUp.mk C B U M S D R A H K P N =>
      [C, B, U, M, S, D, R, A, H, K, P, N]

def constructiveCompletionEquivalenceToEventFlow :
    ConstructiveCompletionEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map constructiveCompletionEquivalenceEncodeBHist
        (constructiveCompletionEquivalenceFields x)

private def constructiveCompletionEquivalenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveCompletionEquivalenceEventAt index rest

def constructiveCompletionEquivalenceFromEventFlow
    (ef : EventFlow) : Option ConstructiveCompletionEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveCompletionEquivalenceUp.mk
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 0 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 1 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 2 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 3 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 4 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 5 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 6 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 7 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 8 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 9 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 10 ef))
      (constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEventAt 11 ef)))

theorem ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveCompletionEquivalenceUp,
      constructiveCompletionEquivalenceFromEventFlow
        (constructiveCompletionEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C B U M S D R A H K P N =>
      change
        some
          (ConstructiveCompletionEquivalenceUp.mk
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist C))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist B))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist U))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist M))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist S))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist D))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist R))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist A))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist H))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist K))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist P))
            (constructiveCompletionEquivalenceDecodeBHist
              (constructiveCompletionEquivalenceEncodeBHist N))) =
          some (ConstructiveCompletionEquivalenceUp.mk C B U M S D R A H K P N)
      rw [ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode B,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode U,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode M,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode S,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode D,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode A,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode K,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode N]

theorem ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveCompletionEquivalenceUp} :
    constructiveCompletionEquivalenceToEventFlow x =
      constructiveCompletionEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveCompletionEquivalenceFromEventFlow
          (constructiveCompletionEquivalenceToEventFlow x) =
        constructiveCompletionEquivalenceFromEventFlow
          (constructiveCompletionEquivalenceToEventFlow y) :=
    congrArg constructiveCompletionEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem constructiveCompletionEquivalence_field_faithful :
    ∀ x y : ConstructiveCompletionEquivalenceUp,
      constructiveCompletionEquivalenceFields x = constructiveCompletionEquivalenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk C₁ B₁ U₁ M₁ S₁ D₁ R₁ A₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk C₂ B₂ U₂ M₂ S₂ D₂ R₂ A₂ H₂ K₂ P₂ N₂ =>
          cases h
          rfl

instance constructiveCompletionEquivalenceBHistCarrier :
    BHistCarrier ConstructiveCompletionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveCompletionEquivalenceToEventFlow
  fromEventFlow := constructiveCompletionEquivalenceFromEventFlow

instance constructiveCompletionEquivalenceChapterTasteGate :
    ChapterTasteGate ConstructiveCompletionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveCompletionEquivalenceFromEventFlow
        (constructiveCompletionEquivalenceToEventFlow x) = some x
    exact ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance constructiveCompletionEquivalenceFieldFaithful :
    FieldFaithful ConstructiveCompletionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constructiveCompletionEquivalenceFields
  field_faithful := constructiveCompletionEquivalence_field_faithful

instance constructiveCompletionEquivalenceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ConstructiveCompletionEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstructiveCompletionEquivalenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ConstructiveCompletionEquivalenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConstructiveCompletionEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveCompletionEquivalenceChapterTasteGate

theorem ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      constructiveCompletionEquivalenceDecodeBHist
        (constructiveCompletionEquivalenceEncodeBHist h) = h) ∧
      (∀ x : ConstructiveCompletionEquivalenceUp,
        constructiveCompletionEquivalenceFromEventFlow
          (constructiveCompletionEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : ConstructiveCompletionEquivalenceUp,
          constructiveCompletionEquivalenceToEventFlow x =
            constructiveCompletionEquivalenceToEventFlow y → x = y) ∧
          constructiveCompletionEquivalenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_decode_encode,
      ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ConstructiveCompletionEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.ConstructiveCompletionEquivalenceUp
