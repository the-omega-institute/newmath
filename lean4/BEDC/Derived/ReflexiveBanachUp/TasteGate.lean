import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReflexiveBanachUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReflexiveBanachUp : Type where
  | mk :
      (banach norm dualWindow evaluation weakReadback boundedBall transport replay provenance
        localName : BHist) →
      ReflexiveBanachUp
  deriving DecidableEq

def reflexiveBanachEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reflexiveBanachEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reflexiveBanachEncodeBHist h

def reflexiveBanachDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reflexiveBanachDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reflexiveBanachDecodeBHist tail)

private theorem reflexiveBanach_decode_encode_bhist :
    ∀ h : BHist, reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def reflexiveBanachFields : ReflexiveBanachUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReflexiveBanachUp.mk banach norm dualWindow evaluation weakReadback boundedBall transport
      replay provenance localName =>
      [banach, norm, dualWindow, evaluation, weakReadback, boundedBall, transport, replay,
        provenance, localName]

def reflexiveBanachToEventFlow : ReflexiveBanachUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map reflexiveBanachEncodeBHist (reflexiveBanachFields x)

private def reflexiveBanachEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => reflexiveBanachEventAtDefault index rest

def reflexiveBanachFromEventFlow : EventFlow → Option ReflexiveBanachUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ReflexiveBanachUp.mk
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 0 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 1 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 2 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 3 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 4 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 5 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 6 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 7 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 8 ef))
        (reflexiveBanachDecodeBHist (reflexiveBanachEventAtDefault 9 ef)))

private theorem reflexiveBanach_round_trip :
    ∀ x : ReflexiveBanachUp,
      reflexiveBanachFromEventFlow (reflexiveBanachToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk banach norm dualWindow evaluation weakReadback boundedBall transport replay provenance
      localName =>
      change
        some
          (ReflexiveBanachUp.mk
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist banach))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist norm))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist dualWindow))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist evaluation))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist weakReadback))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist boundedBall))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist transport))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist replay))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist provenance))
            (reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist localName))) =
          some
            (ReflexiveBanachUp.mk banach norm dualWindow evaluation weakReadback boundedBall
              transport replay provenance localName)
      rw [reflexiveBanach_decode_encode_bhist banach,
        reflexiveBanach_decode_encode_bhist norm,
        reflexiveBanach_decode_encode_bhist dualWindow,
        reflexiveBanach_decode_encode_bhist evaluation,
        reflexiveBanach_decode_encode_bhist weakReadback,
        reflexiveBanach_decode_encode_bhist boundedBall,
        reflexiveBanach_decode_encode_bhist transport,
        reflexiveBanach_decode_encode_bhist replay,
        reflexiveBanach_decode_encode_bhist provenance,
        reflexiveBanach_decode_encode_bhist localName]

private theorem reflexiveBanachToEventFlow_injective {x y : ReflexiveBanachUp} :
    reflexiveBanachToEventFlow x = reflexiveBanachToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reflexiveBanachFromEventFlow (reflexiveBanachToEventFlow x) =
        reflexiveBanachFromEventFlow (reflexiveBanachToEventFlow y) :=
    congrArg reflexiveBanachFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reflexiveBanach_round_trip x).symm
      (Eq.trans hread (reflexiveBanach_round_trip y)))

private theorem reflexiveBanach_field_faithful :
    ∀ x y : ReflexiveBanachUp, reflexiveBanachFields x = reflexiveBanachFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk banach₁ norm₁ dualWindow₁ evaluation₁ weakReadback₁ boundedBall₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk banach₂ norm₂ dualWindow₂ evaluation₂ weakReadback₂ boundedBall₂ transport₂ replay₂
          provenance₂ localName₂ =>
          cases hfields
          rfl

instance reflexiveBanachBHistCarrier : BHistCarrier ReflexiveBanachUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reflexiveBanachToEventFlow
  fromEventFlow := reflexiveBanachFromEventFlow

instance reflexiveBanachChapterTasteGate : ChapterTasteGate ReflexiveBanachUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reflexiveBanachFromEventFlow (reflexiveBanachToEventFlow x) = some x
    exact reflexiveBanach_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reflexiveBanachToEventFlow_injective heq)

instance reflexiveBanachFieldFaithful : FieldFaithful ReflexiveBanachUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reflexiveBanachFields
  field_faithful := reflexiveBanach_field_faithful

instance reflexiveBanachNontrivial : Nontrivial ReflexiveBanachUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReflexiveBanachUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ReflexiveBanachUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ReflexiveBanachUp :=
  -- BEDC touchpoint anchor: BHist BMark
  reflexiveBanachChapterTasteGate

theorem ReflexiveBanachTasteGate_single_carrier_alignment :
    (∀ h : BHist, reflexiveBanachDecodeBHist (reflexiveBanachEncodeBHist h) = h) ∧
      (∀ x : ReflexiveBanachUp,
        reflexiveBanachFromEventFlow (reflexiveBanachToEventFlow x) = some x) ∧
        (∀ x y : ReflexiveBanachUp,
          reflexiveBanachToEventFlow x = reflexiveBanachToEventFlow y -> x = y) ∧
          reflexiveBanachEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : ReflexiveBanachUp, reflexiveBanachFields x = reflexiveBanachFields y ->
              x = y) ∧
              (∃ x y : ReflexiveBanachUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact reflexiveBanach_decode_encode_bhist
  · constructor
    · exact reflexiveBanach_round_trip
    · constructor
      · intro x y heq
        exact reflexiveBanachToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact reflexiveBanach_field_faithful
          · exact
              ⟨ReflexiveBanachUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                ReflexiveBanachUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.ReflexiveBanachUp
