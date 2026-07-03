import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchyConvergenceModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveCauchyConvergenceModulusUp : Type where
  | mk (D W R S M H C P N : BHist) : EffectiveCauchyConvergenceModulusUp
  deriving DecidableEq

def effectiveCauchyConvergenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchyConvergenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchyConvergenceModulusEncodeBHist h

def effectiveCauchyConvergenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchyConvergenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchyConvergenceModulusDecodeBHist tail)

private theorem EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchyConvergenceModulusFields :
    EffectiveCauchyConvergenceModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchyConvergenceModulusUp.mk D W R S M H C P N =>
      [D, W, R, S, M, H, C, P, N]

def effectiveCauchyConvergenceModulusToEventFlow :
    EffectiveCauchyConvergenceModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (effectiveCauchyConvergenceModulusFields x).map
        effectiveCauchyConvergenceModulusEncodeBHist

private def effectiveCauchyConvergenceModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      effectiveCauchyConvergenceModulusEventAtDefault index rest

def effectiveCauchyConvergenceModulusFromEventFlow
    (ef : EventFlow) : Option EffectiveCauchyConvergenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectiveCauchyConvergenceModulusUp.mk
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 0 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 1 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 2 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 3 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 4 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 5 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 6 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 7 ef))
      (effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEventAtDefault 8 ef)))

private theorem EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EffectiveCauchyConvergenceModulusUp,
      effectiveCauchyConvergenceModulusFromEventFlow
        (effectiveCauchyConvergenceModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R S M H C P N =>
      change
        some
          (EffectiveCauchyConvergenceModulusUp.mk
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist D))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist W))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist R))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist S))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist M))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist H))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist C))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist P))
            (effectiveCauchyConvergenceModulusDecodeBHist
              (effectiveCauchyConvergenceModulusEncodeBHist N))) =
          some (EffectiveCauchyConvergenceModulusUp.mk D W R S M H C P N)
      rw [EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode D,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode W,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode R,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode S,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode M,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode H,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode C,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode P,
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EffectiveCauchyConvergenceModulusUp} :
    effectiveCauchyConvergenceModulusToEventFlow x =
        effectiveCauchyConvergenceModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchyConvergenceModulusFromEventFlow
          (effectiveCauchyConvergenceModulusToEventFlow x) =
        effectiveCauchyConvergenceModulusFromEventFlow
          (effectiveCauchyConvergenceModulusToEventFlow y) :=
    congrArg effectiveCauchyConvergenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_round_trip y)))

instance effectiveCauchyConvergenceModulusBHistCarrier :
    BHistCarrier EffectiveCauchyConvergenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchyConvergenceModulusToEventFlow
  fromEventFlow := effectiveCauchyConvergenceModulusFromEventFlow

instance effectiveCauchyConvergenceModulusChapterTasteGate :
    ChapterTasteGate EffectiveCauchyConvergenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      effectiveCauchyConvergenceModulusFromEventFlow
          (effectiveCauchyConvergenceModulusToEventFlow x) = some x
    exact EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate EffectiveCauchyConvergenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveCauchyConvergenceModulusChapterTasteGate

theorem EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      effectiveCauchyConvergenceModulusDecodeBHist
        (effectiveCauchyConvergenceModulusEncodeBHist h) = h) ∧
      (∀ x : EffectiveCauchyConvergenceModulusUp,
        effectiveCauchyConvergenceModulusFromEventFlow
          (effectiveCauchyConvergenceModulusToEventFlow x) = some x) ∧
        (∀ x y : EffectiveCauchyConvergenceModulusUp,
          effectiveCauchyConvergenceModulusToEventFlow x =
              effectiveCauchyConvergenceModulusToEventFlow y →
            x = y) ∧
          effectiveCauchyConvergenceModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_decode_encode,
      EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        EffectiveCauchyConvergenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      rfl⟩

end BEDC.Derived.EffectiveCauchyConvergenceModulusUp
