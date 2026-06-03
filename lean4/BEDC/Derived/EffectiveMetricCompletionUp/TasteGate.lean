import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveMetricCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveMetricCompletionUp : Type where
  | mk (M L A S R E H C P N : BHist) : EffectiveMetricCompletionUp
  deriving DecidableEq

def effectiveMetricCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveMetricCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveMetricCompletionEncodeBHist h

def effectiveMetricCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveMetricCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveMetricCompletionDecodeBHist tail)

private theorem EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveMetricCompletionFields : EffectiveMetricCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveMetricCompletionUp.mk M L A S R E H C P N => [M, L, A, S, R, E, H, C, P, N]

def effectiveMetricCompletionToEventFlow : EffectiveMetricCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (effectiveMetricCompletionFields x).map effectiveMetricCompletionEncodeBHist

private def effectiveMetricCompletionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveMetricCompletionEventAtDefault index rest

def effectiveMetricCompletionFromEventFlow (ef : EventFlow) :
    Option EffectiveMetricCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectiveMetricCompletionUp.mk
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 0 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 1 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 2 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 3 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 4 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 5 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 6 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 7 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 8 ef))
      (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEventAtDefault 9 ef)))

private theorem EffectiveMetricCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EffectiveMetricCompletionUp,
      effectiveMetricCompletionFromEventFlow (effectiveMetricCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M L A S R E H C P N =>
      change
        some
          (EffectiveMetricCompletionUp.mk
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist M))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist L))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist A))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist S))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist R))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist E))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist H))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist C))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist P))
            (effectiveMetricCompletionDecodeBHist (effectiveMetricCompletionEncodeBHist N))) =
          some (EffectiveMetricCompletionUp.mk M L A S R E H C P N)
      rw [EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode M,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode L,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode A,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode S,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode R,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode E,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode H,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode C,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode P,
        EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode N]

private theorem EffectiveMetricCompletionTasteGate_single_carrier_alignment_injective
    {x y : EffectiveMetricCompletionUp} :
    effectiveMetricCompletionToEventFlow x = effectiveMetricCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveMetricCompletionFromEventFlow (effectiveMetricCompletionToEventFlow x) =
        effectiveMetricCompletionFromEventFlow (effectiveMetricCompletionToEventFlow y) :=
    congrArg effectiveMetricCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EffectiveMetricCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EffectiveMetricCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance effectiveMetricCompletionBHistCarrier : BHistCarrier EffectiveMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveMetricCompletionToEventFlow
  fromEventFlow := effectiveMetricCompletionFromEventFlow

instance effectiveMetricCompletionChapterTasteGate :
    ChapterTasteGate EffectiveMetricCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveMetricCompletionFromEventFlow (effectiveMetricCompletionToEventFlow x) = some x
    exact EffectiveMetricCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EffectiveMetricCompletionTasteGate_single_carrier_alignment_injective heq)

theorem EffectiveMetricCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist, effectiveMetricCompletionDecodeBHist
      (effectiveMetricCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EffectiveMetricCompletionUp) ∧
        Nonempty (ChapterTasteGate EffectiveMetricCompletionUp) ∧
          effectiveMetricCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EffectiveMetricCompletionTasteGate_single_carrier_alignment_decode,
      ⟨⟨effectiveMetricCompletionBHistCarrier⟩,
        ⟨effectiveMetricCompletionChapterTasteGate⟩,
        rfl⟩⟩

end BEDC.Derived.EffectiveMetricCompletionUp
