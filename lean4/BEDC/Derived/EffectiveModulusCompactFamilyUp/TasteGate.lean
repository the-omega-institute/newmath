import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveModulusCompactFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveModulusCompactFamilyUp : Type where
  | mk (K U M Q W H C P N : BHist) : EffectiveModulusCompactFamilyUp
  deriving DecidableEq

def effectiveModulusCompactFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveModulusCompactFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveModulusCompactFamilyEncodeBHist h

def effectiveModulusCompactFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveModulusCompactFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveModulusCompactFamilyDecodeBHist tail)

private theorem EffectiveModulusCompactFamilyTasteGate_decode_encode :
    ∀ h : BHist,
      effectiveModulusCompactFamilyDecodeBHist
          (effectiveModulusCompactFamilyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveModulusCompactFamilyFields :
    EffectiveModulusCompactFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveModulusCompactFamilyUp.mk K U M Q W H C P N =>
      [K, U, M, Q, W, H, C, P, N]

def effectiveModulusCompactFamilyToEventFlow :
    EffectiveModulusCompactFamilyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (effectiveModulusCompactFamilyFields x).map
    effectiveModulusCompactFamilyEncodeBHist

private def effectiveModulusCompactFamilyRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveModulusCompactFamilyRawAt index rest

private def effectiveModulusCompactFamilyLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => effectiveModulusCompactFamilyLengthEq index rest

def effectiveModulusCompactFamilyFromEventFlow :
    EventFlow → Option EffectiveModulusCompactFamilyUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match effectiveModulusCompactFamilyLengthEq 9 flow with
      | true =>
          some
            (EffectiveModulusCompactFamilyUp.mk
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 0 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 1 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 2 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 3 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 4 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 5 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 6 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 7 flow))
              (effectiveModulusCompactFamilyDecodeBHist
                (effectiveModulusCompactFamilyRawAt 8 flow)))
      | false => none

private theorem effectiveModulusCompactFamily_round_trip :
    ∀ x : EffectiveModulusCompactFamilyUp,
      effectiveModulusCompactFamilyFromEventFlow
          (effectiveModulusCompactFamilyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K U M Q W H C P N =>
      change
        some
          (EffectiveModulusCompactFamilyUp.mk
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist K))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist U))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist M))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist Q))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist W))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist H))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist C))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist P))
            (effectiveModulusCompactFamilyDecodeBHist
              (effectiveModulusCompactFamilyEncodeBHist N))) =
          some (EffectiveModulusCompactFamilyUp.mk K U M Q W H C P N)
      rw [EffectiveModulusCompactFamilyTasteGate_decode_encode K,
        EffectiveModulusCompactFamilyTasteGate_decode_encode U,
        EffectiveModulusCompactFamilyTasteGate_decode_encode M,
        EffectiveModulusCompactFamilyTasteGate_decode_encode Q,
        EffectiveModulusCompactFamilyTasteGate_decode_encode W,
        EffectiveModulusCompactFamilyTasteGate_decode_encode H,
        EffectiveModulusCompactFamilyTasteGate_decode_encode C,
        EffectiveModulusCompactFamilyTasteGate_decode_encode P,
        EffectiveModulusCompactFamilyTasteGate_decode_encode N]

private theorem effectiveModulusCompactFamilyToEventFlow_injective
    {x y : EffectiveModulusCompactFamilyUp} :
    effectiveModulusCompactFamilyToEventFlow x =
        effectiveModulusCompactFamilyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveModulusCompactFamilyFromEventFlow
          (effectiveModulusCompactFamilyToEventFlow x) =
        effectiveModulusCompactFamilyFromEventFlow
          (effectiveModulusCompactFamilyToEventFlow y) :=
    congrArg effectiveModulusCompactFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveModulusCompactFamily_round_trip x).symm
      (Eq.trans hread (effectiveModulusCompactFamily_round_trip y)))

private theorem effectiveModulusCompactFamily_fields_faithful :
    ∀ x y : EffectiveModulusCompactFamilyUp,
      effectiveModulusCompactFamilyFields x = effectiveModulusCompactFamilyFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ U₁ M₁ Q₁ W₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ U₂ M₂ Q₂ W₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance effectiveModulusCompactFamilyBHistCarrier :
    BHistCarrier EffectiveModulusCompactFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveModulusCompactFamilyToEventFlow
  fromEventFlow := effectiveModulusCompactFamilyFromEventFlow

instance effectiveModulusCompactFamilyChapterTasteGate :
    ChapterTasteGate EffectiveModulusCompactFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      effectiveModulusCompactFamilyFromEventFlow
          (effectiveModulusCompactFamilyToEventFlow x) =
        some x
    exact effectiveModulusCompactFamily_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveModulusCompactFamilyToEventFlow_injective heq)

instance effectiveModulusCompactFamilyFieldFaithful :
    FieldFaithful EffectiveModulusCompactFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := effectiveModulusCompactFamilyFields
  field_faithful := effectiveModulusCompactFamily_fields_faithful

def taste_gate : ChapterTasteGate EffectiveModulusCompactFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveModulusCompactFamilyChapterTasteGate

theorem EffectiveModulusCompactFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      effectiveModulusCompactFamilyDecodeBHist
          (effectiveModulusCompactFamilyEncodeBHist h) =
        h) ∧
      (∀ x : EffectiveModulusCompactFamilyUp,
        effectiveModulusCompactFamilyFromEventFlow
            (effectiveModulusCompactFamilyToEventFlow x) =
          some x) ∧
        (∀ x y : EffectiveModulusCompactFamilyUp,
          effectiveModulusCompactFamilyToEventFlow x =
              effectiveModulusCompactFamilyToEventFlow y ->
            x = y) ∧
          effectiveModulusCompactFamilyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨EffectiveModulusCompactFamilyTasteGate_decode_encode,
      effectiveModulusCompactFamily_round_trip,
      (fun _ _ heq => effectiveModulusCompactFamilyToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EffectiveModulusCompactFamilyUp
