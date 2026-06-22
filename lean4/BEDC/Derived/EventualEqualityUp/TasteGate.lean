import BEDC.Derived.EventualEqualityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EventualEqualityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EventualEqualityUp : Type where
  | mk (L R T A Q H C P N : BHist) : EventualEqualityUp

def eventualEqualityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eventualEqualityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eventualEqualityEncodeBHist h

def eventualEqualityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eventualEqualityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eventualEqualityDecodeBHist tail)

private theorem EventualEqualityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, eventualEqualityDecodeBHist (eventualEqualityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eventualEqualityFields : EventualEqualityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EventualEqualityUp.mk L R T A Q H C P N => [L, R, T, A, Q, H, C, P, N]

def eventualEqualityToEventFlow : EventualEqualityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eventualEqualityFields x).map eventualEqualityEncodeBHist

private def eventualEqualityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eventualEqualityEventAt index rest

def eventualEqualityFromEventFlow (ef : EventFlow) : Option EventualEqualityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EventualEqualityUp.mk
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 0 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 1 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 2 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 3 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 4 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 5 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 6 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 7 ef))
      (eventualEqualityDecodeBHist (eventualEqualityEventAt 8 ef)))

private theorem EventualEqualityTasteGate_single_carrier_alignment_round_trip
    (x : EventualEqualityUp) :
    eventualEqualityFromEventFlow (eventualEqualityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L R T A Q H C P N =>
      change
        some
          (EventualEqualityUp.mk
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist L))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist R))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist T))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist A))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist Q))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist H))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist C))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist P))
            (eventualEqualityDecodeBHist (eventualEqualityEncodeBHist N))) =
          some (EventualEqualityUp.mk L R T A Q H C P N)
      rw [EventualEqualityTasteGate_single_carrier_alignment_decode_encode L,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode R,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode T,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode A,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode Q,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode H,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode C,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode P,
        EventualEqualityTasteGate_single_carrier_alignment_decode_encode N]

private theorem EventualEqualityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EventualEqualityUp} :
    eventualEqualityToEventFlow x = eventualEqualityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eventualEqualityFromEventFlow (eventualEqualityToEventFlow x) =
        eventualEqualityFromEventFlow (eventualEqualityToEventFlow y) :=
    congrArg eventualEqualityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EventualEqualityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EventualEqualityTasteGate_single_carrier_alignment_round_trip y)))

private theorem EventualEqualityTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : EventualEqualityUp,
      eventualEqualityFields x = eventualEqualityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ R₁ T₁ A₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ R₂ T₂ A₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance eventualEqualityBHistCarrier : BHistCarrier EventualEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eventualEqualityToEventFlow
  fromEventFlow := eventualEqualityFromEventFlow

instance eventualEqualityChapterTasteGate : ChapterTasteGate EventualEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eventualEqualityFromEventFlow (eventualEqualityToEventFlow x) = some x
    exact EventualEqualityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EventualEqualityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance eventualEqualityFieldFaithful : FieldFaithful EventualEqualityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eventualEqualityFields
  field_faithful := EventualEqualityTasteGate_single_carrier_alignment_fields_faithful

theorem EventualEqualityTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier EventualEqualityUp) ∧
      Nonempty (ChapterTasteGate EventualEqualityUp) ∧
        Nonempty (FieldFaithful EventualEqualityUp) ∧
          eventualEqualityDecodeBHist (eventualEqualityEncodeBHist BHist.Empty) = BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro eventualEqualityBHistCarrier,
      Nonempty.intro eventualEqualityChapterTasteGate,
      Nonempty.intro eventualEqualityFieldFaithful,
      EventualEqualityTasteGate_single_carrier_alignment_decode_encode BHist.Empty⟩

end BEDC.Derived.EventualEqualityUp.TasteGate
