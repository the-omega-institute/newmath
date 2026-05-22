import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedMetricReflectionUp : Type where
  | mk (x s a u z h c p n : BHist) : SeparatedMetricReflectionUp
  deriving DecidableEq

def separatedMetricReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedMetricReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedMetricReflectionEncodeBHist h

def separatedMetricReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedMetricReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedMetricReflectionDecodeBHist tail)

private theorem separatedMetricReflection_decode_encode_bhist :
    ∀ h : BHist, separatedMetricReflectionDecodeBHist
      (separatedMetricReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedMetricReflectionToEventFlow : SeparatedMetricReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedMetricReflectionUp.mk x s a u z h c p n =>
      [[BMark.b0],
        separatedMetricReflectionEncodeBHist x,
        [BMark.b1, BMark.b0],
        separatedMetricReflectionEncodeBHist s,
        [BMark.b1, BMark.b1, BMark.b0],
        separatedMetricReflectionEncodeBHist a,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedMetricReflectionEncodeBHist u,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedMetricReflectionEncodeBHist z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedMetricReflectionEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        separatedMetricReflectionEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        separatedMetricReflectionEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        separatedMetricReflectionEncodeBHist n]

private def separatedMetricReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => separatedMetricReflectionEventAtDefault index rest

def separatedMetricReflectionFromEventFlow
    (ef : EventFlow) : Option SeparatedMetricReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SeparatedMetricReflectionUp.mk
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 1 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 3 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 5 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 7 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 9 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 11 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 13 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 15 ef))
      (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEventAtDefault 17 ef)))

private theorem separatedMetricReflection_round_trip :
    ∀ x : SeparatedMetricReflectionUp,
      separatedMetricReflectionFromEventFlow (separatedMetricReflectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk x s a u z h c p n =>
      change
        some
          (SeparatedMetricReflectionUp.mk
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist x))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist s))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist a))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist u))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist z))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist h))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist c))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist p))
            (separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist n))) =
          some (SeparatedMetricReflectionUp.mk x s a u z h c p n)
      rw [separatedMetricReflection_decode_encode_bhist x,
        separatedMetricReflection_decode_encode_bhist s,
        separatedMetricReflection_decode_encode_bhist a,
        separatedMetricReflection_decode_encode_bhist u,
        separatedMetricReflection_decode_encode_bhist z,
        separatedMetricReflection_decode_encode_bhist h,
        separatedMetricReflection_decode_encode_bhist c,
        separatedMetricReflection_decode_encode_bhist p,
        separatedMetricReflection_decode_encode_bhist n]

private theorem separatedMetricReflectionToEventFlow_injective
    {x y : SeparatedMetricReflectionUp} :
    separatedMetricReflectionToEventFlow x = separatedMetricReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedMetricReflectionFromEventFlow (separatedMetricReflectionToEventFlow x) =
        separatedMetricReflectionFromEventFlow (separatedMetricReflectionToEventFlow y) :=
    congrArg separatedMetricReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (separatedMetricReflection_round_trip x).symm
      (Eq.trans hread (separatedMetricReflection_round_trip y)))

private def separatedMetricReflectionFields : SeparatedMetricReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedMetricReflectionUp.mk x s a u z h c p n => [x, s, a, u, z, h, c, p, n]

private theorem separatedMetricReflection_field_faithful :
    ∀ x y : SeparatedMetricReflectionUp,
      separatedMetricReflectionFields x = separatedMetricReflectionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token₁ token₂ hfields
  cases token₁ with
  | mk x₁ s₁ a₁ u₁ z₁ h₁ c₁ p₁ n₁ =>
      cases token₂ with
      | mk x₂ s₂ a₂ u₂ z₂ h₂ c₂ p₂ n₂ =>
          cases hfields
          rfl

instance separatedMetricReflectionBHistCarrier :
    BHistCarrier SeparatedMetricReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedMetricReflectionToEventFlow
  fromEventFlow := separatedMetricReflectionFromEventFlow

instance separatedMetricReflectionChapterTasteGate :
    ChapterTasteGate SeparatedMetricReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separatedMetricReflectionFromEventFlow (separatedMetricReflectionToEventFlow x) =
      some x
    exact separatedMetricReflection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separatedMetricReflectionToEventFlow_injective heq)

instance separatedMetricReflectionFieldFaithful :
    FieldFaithful SeparatedMetricReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := separatedMetricReflectionFields
  field_faithful := separatedMetricReflection_field_faithful

instance separatedMetricReflectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SeparatedMetricReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeparatedMetricReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SeparatedMetricReflectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SeparatedMetricReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  separatedMetricReflectionChapterTasteGate

private theorem SeparatedMetricReflectionTasteGate_single_carrier_alignment_instances :
    Nonempty (ChapterTasteGate SeparatedMetricReflectionUp) ∧
      Nonempty (FieldFaithful SeparatedMetricReflectionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SeparatedMetricReflectionUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨separatedMetricReflectionChapterTasteGate⟩,
      ⟨separatedMetricReflectionFieldFaithful⟩,
      ⟨separatedMetricReflectionNontrivial⟩⟩

theorem SeparatedMetricReflectionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SeparatedMetricReflectionUp) ∧
      Nonempty (FieldFaithful SeparatedMetricReflectionUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SeparatedMetricReflectionUp) ∧
          (∀ h : BHist,
            separatedMetricReflectionDecodeBHist (separatedMetricReflectionEncodeBHist h) =
              h) ∧
            (∀ x : SeparatedMetricReflectionUp,
              separatedMetricReflectionFromEventFlow (separatedMetricReflectionToEventFlow x) =
                some x) ∧
              (∀ x y : SeparatedMetricReflectionUp,
                separatedMetricReflectionToEventFlow x =
                  separatedMetricReflectionToEventFlow y → x = y) ∧
                separatedMetricReflectionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  have hinstances :=
    SeparatedMetricReflectionTasteGate_single_carrier_alignment_instances
  exact
    ⟨hinstances.1,
      hinstances.2.1,
      hinstances.2.2,
      separatedMetricReflection_decode_encode_bhist,
      separatedMetricReflection_round_trip,
      (fun _ _ heq => separatedMetricReflectionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SeparatedMetricReflectionUp
