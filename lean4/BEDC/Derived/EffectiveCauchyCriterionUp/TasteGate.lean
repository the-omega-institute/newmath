import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchyCriterionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveCauchyCriterionUp : Type where
  | mk (Q M S T D R L H C P N : BHist) : EffectiveCauchyCriterionUp
  deriving DecidableEq

def effectiveCauchyCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchyCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchyCriterionEncodeBHist h

def effectiveCauchyCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchyCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchyCriterionDecodeBHist tail)

private theorem EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchyCriterionToEventFlow : EffectiveCauchyCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchyCriterionUp.mk Q M S T D R L H C P N =>
      [[BMark.b0],
        effectiveCauchyCriterionEncodeBHist Q,
        [BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        effectiveCauchyCriterionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        effectiveCauchyCriterionEncodeBHist N]

private def effectiveCauchyCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveCauchyCriterionEventAtDefault index rest

def effectiveCauchyCriterionFromEventFlow :
    EventFlow → Option EffectiveCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EffectiveCauchyCriterionUp.mk
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 1 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 3 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 5 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 7 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 9 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 11 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 13 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 15 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 17 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 19 ef))
        (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEventAtDefault 21 ef)))

private theorem EffectiveCauchyCriterionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EffectiveCauchyCriterionUp,
      effectiveCauchyCriterionFromEventFlow
        (effectiveCauchyCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q M S T D R L H C P N =>
      change
        some
          (EffectiveCauchyCriterionUp.mk
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist Q))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist M))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist S))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist T))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist D))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist R))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist L))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist H))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist C))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist P))
            (effectiveCauchyCriterionDecodeBHist (effectiveCauchyCriterionEncodeBHist N))) =
          some (EffectiveCauchyCriterionUp.mk Q M S T D R L H C P N)
      rw [EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode Q,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode M,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode S,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode T,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode D,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode R,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode L,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode H,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode C,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode P,
        EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode N]

private theorem EffectiveCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EffectiveCauchyCriterionUp} :
    effectiveCauchyCriterionToEventFlow x =
      effectiveCauchyCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchyCriterionFromEventFlow
          (effectiveCauchyCriterionToEventFlow x) =
        effectiveCauchyCriterionFromEventFlow
          (effectiveCauchyCriterionToEventFlow y) :=
    congrArg effectiveCauchyCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EffectiveCauchyCriterionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EffectiveCauchyCriterionTasteGate_single_carrier_alignment_round_trip y)))

instance effectiveCauchyCriterionBHistCarrier :
    BHistCarrier EffectiveCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchyCriterionToEventFlow
  fromEventFlow := effectiveCauchyCriterionFromEventFlow

instance effectiveCauchyCriterionChapterTasteGate :
    ChapterTasteGate EffectiveCauchyCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      effectiveCauchyCriterionFromEventFlow
        (effectiveCauchyCriterionToEventFlow x) = some x
    exact EffectiveCauchyCriterionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EffectiveCauchyCriterionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate EffectiveCauchyCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveCauchyCriterionChapterTasteGate

theorem EffectiveCauchyCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist, effectiveCauchyCriterionDecodeBHist
      (effectiveCauchyCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EffectiveCauchyCriterionUp) ∧
        Nonempty (ChapterTasteGate EffectiveCauchyCriterionUp) ∧
          effectiveCauchyCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨EffectiveCauchyCriterionTasteGate_single_carrier_alignment_decode_encode,
      ⟨effectiveCauchyCriterionBHistCarrier⟩,
      ⟨effectiveCauchyCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.EffectiveCauchyCriterionUp.TasteGate
