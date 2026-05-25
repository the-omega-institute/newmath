import BEDC.Derived.EffectiveCompletionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def effectiveCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCompletionEncodeBHist h

def effectiveCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCompletionDecodeBHist tail)

private theorem effectiveCompletion_decode_encode_bhist :
    ∀ h : BHist, effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCompletionFields : EffectiveCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCompletionUp.mk E Q K W R D A U H C P N => [E, Q, K, W, R, D, A, U, H, C, P, N]

def effectiveCompletionToEventFlow : EffectiveCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (effectiveCompletionFields x).map effectiveCompletionEncodeBHist

private def effectiveCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveCompletionEventAtDefault index rest

def effectiveCompletionFromEventFlow (ef : EventFlow) : Option EffectiveCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectiveCompletionUp.mk
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 0 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 1 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 2 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 3 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 4 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 5 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 6 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 7 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 8 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 9 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 10 ef))
      (effectiveCompletionDecodeBHist (effectiveCompletionEventAtDefault 11 ef)))

private theorem effectiveCompletion_round_trip :
    ∀ x : EffectiveCompletionUp,
      effectiveCompletionFromEventFlow (effectiveCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E Q K W R D A U H C P N =>
      change
        some
          (EffectiveCompletionUp.mk
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist E))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist Q))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist K))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist W))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist R))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist D))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist A))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist U))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist H))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist C))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist P))
            (effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist N))) =
          some (EffectiveCompletionUp.mk E Q K W R D A U H C P N)
      rw [effectiveCompletion_decode_encode_bhist E, effectiveCompletion_decode_encode_bhist Q,
        effectiveCompletion_decode_encode_bhist K, effectiveCompletion_decode_encode_bhist W,
        effectiveCompletion_decode_encode_bhist R, effectiveCompletion_decode_encode_bhist D,
        effectiveCompletion_decode_encode_bhist A, effectiveCompletion_decode_encode_bhist U,
        effectiveCompletion_decode_encode_bhist H, effectiveCompletion_decode_encode_bhist C,
        effectiveCompletion_decode_encode_bhist P, effectiveCompletion_decode_encode_bhist N]

private theorem effectiveCompletionToEventFlow_injective {x y : EffectiveCompletionUp} :
    effectiveCompletionToEventFlow x = effectiveCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCompletionFromEventFlow (effectiveCompletionToEventFlow x) =
        effectiveCompletionFromEventFlow (effectiveCompletionToEventFlow y) :=
    congrArg effectiveCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveCompletion_round_trip x).symm
      (Eq.trans hread (effectiveCompletion_round_trip y)))

private theorem effectiveCompletion_field_faithful :
    ∀ x y : EffectiveCompletionUp, effectiveCompletionFields x = effectiveCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E Q K W R D A U H C P N =>
      cases y with
      | mk E' Q' K' W' R' D' A' U' H' C' P' N' =>
          cases hfields
          rfl

instance effectiveCompletionBHistCarrier : BHistCarrier EffectiveCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCompletionToEventFlow
  fromEventFlow := effectiveCompletionFromEventFlow

instance effectiveCompletionChapterTasteGate : ChapterTasteGate EffectiveCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveCompletionFromEventFlow (effectiveCompletionToEventFlow x) = some x
    exact effectiveCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveCompletionToEventFlow_injective heq)

instance effectiveCompletionFieldFaithful : FieldFaithful EffectiveCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectiveCompletionFields
  field_faithful := effectiveCompletion_field_faithful

instance effectiveCompletionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EffectiveCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EffectiveCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EffectiveCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EffectiveCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveCompletionChapterTasteGate

theorem EffectiveCompletionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EffectiveCompletionUp) ∧
      Nonempty (FieldFaithful EffectiveCompletionUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial EffectiveCompletionUp) ∧
      (∀ h : BHist, effectiveCompletionDecodeBHist (effectiveCompletionEncodeBHist h) = h) ∧
      (∀ x : EffectiveCompletionUp,
        effectiveCompletionFromEventFlow (effectiveCompletionToEventFlow x) = some x) ∧
      (∀ x y : EffectiveCompletionUp,
        effectiveCompletionToEventFlow x = effectiveCompletionToEventFlow y → x = y) ∧
      effectiveCompletionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨effectiveCompletionChapterTasteGate⟩, ⟨effectiveCompletionFieldFaithful⟩,
      ⟨effectiveCompletionNontrivial⟩, effectiveCompletion_decode_encode_bhist,
      effectiveCompletion_round_trip,
      (fun _ _ heq => effectiveCompletionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.EffectiveCompletionUp
