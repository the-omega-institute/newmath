import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonoidalCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonoidalCompletionUp : Type where
  | mk (M U V P A S H C G N : BHist) : MonoidalCompletionUp
  deriving DecidableEq

def monoidalCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monoidalCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monoidalCompletionEncodeBHist h

def monoidalCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monoidalCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monoidalCompletionDecodeBHist tail)

private theorem MonoidalCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monoidalCompletionFields : MonoidalCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonoidalCompletionUp.mk M U V P A S H C G N => [M, U, V, P, A, S, H, C, G, N]

def monoidalCompletionToEventFlow : MonoidalCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (monoidalCompletionFields x).map monoidalCompletionEncodeBHist

private def monoidalCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monoidalCompletionEventAtDefault index rest

def monoidalCompletionFromEventFlow (ef : EventFlow) : Option MonoidalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonoidalCompletionUp.mk
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 0 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 1 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 2 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 3 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 4 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 5 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 6 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 7 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 8 ef))
      (monoidalCompletionDecodeBHist (monoidalCompletionEventAtDefault 9 ef)))

private theorem MonoidalCompletionTasteGate_single_carrier_alignment_round_trip
    (x : MonoidalCompletionUp) :
    monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M U V P A S H C G N =>
      change
        some
          (MonoidalCompletionUp.mk
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist M))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist U))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist V))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist P))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist A))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist S))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist H))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist C))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist G))
            (monoidalCompletionDecodeBHist (monoidalCompletionEncodeBHist N))) =
          some (MonoidalCompletionUp.mk M U V P A S H C G N)
      rw [MonoidalCompletionTasteGate_single_carrier_alignment_decode M,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode U,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode V,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode P,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode A,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode S,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode H,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode C,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode G,
        MonoidalCompletionTasteGate_single_carrier_alignment_decode N]

private theorem MonoidalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MonoidalCompletionUp} :
    monoidalCompletionToEventFlow x = monoidalCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow x) =
        monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow y) :=
    congrArg monoidalCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MonoidalCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MonoidalCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem MonoidalCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MonoidalCompletionUp, monoidalCompletionFields x = monoidalCompletionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ U₁ V₁ P₁ A₁ S₁ H₁ C₁ G₁ N₁ =>
      cases y with
      | mk M₂ U₂ V₂ P₂ A₂ S₂ H₂ C₂ G₂ N₂ =>
          cases hfields
          rfl

instance monoidalCompletionBHistCarrier : BHistCarrier MonoidalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monoidalCompletionToEventFlow
  fromEventFlow := monoidalCompletionFromEventFlow

instance monoidalCompletionChapterTasteGate : ChapterTasteGate MonoidalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow x) = some x
    exact MonoidalCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MonoidalCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance monoidalCompletionFieldFaithful : FieldFaithful MonoidalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := monoidalCompletionFields
  field_faithful := MonoidalCompletionTasteGate_single_carrier_alignment_fields_faithful

instance monoidalCompletionNontrivial : Nontrivial MonoidalCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MonoidalCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MonoidalCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MonoidalCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monoidalCompletionChapterTasteGate

theorem MonoidalCompletionTasteGate_single_carrier_alignment :
    ∃ x : MonoidalCompletionUp,
      monoidalCompletionFromEventFlow (monoidalCompletionToEventFlow x) = some x ∧
        BHistCarrier.toEventFlow x = monoidalCompletionToEventFlow x := by
  -- BEDC touchpoint anchor: BHist BMark
  refine
    ⟨MonoidalCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, ?_, ?_⟩
  · exact MonoidalCompletionTasteGate_single_carrier_alignment_round_trip _
  · rfl

end BEDC.Derived.MonoidalCompletionUp
