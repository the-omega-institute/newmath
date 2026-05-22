import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchySequenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveCauchySequenceUp : Type where
  | mk (S M W D Q E H C P N : BHist) : EffectiveCauchySequenceUp
  deriving DecidableEq

def effectiveCauchySequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchySequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchySequenceEncodeBHist h

def effectiveCauchySequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchySequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchySequenceDecodeBHist tail)

private theorem effectiveCauchySequence_decode_encode_bhist :
    ∀ h : BHist,
      effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchySequenceToEventFlow : EffectiveCauchySequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchySequenceUp.mk S M W D Q E H C P N =>
      [effectiveCauchySequenceEncodeBHist S,
        effectiveCauchySequenceEncodeBHist M,
        effectiveCauchySequenceEncodeBHist W,
        effectiveCauchySequenceEncodeBHist D,
        effectiveCauchySequenceEncodeBHist Q,
        effectiveCauchySequenceEncodeBHist E,
        effectiveCauchySequenceEncodeBHist H,
        effectiveCauchySequenceEncodeBHist C,
        effectiveCauchySequenceEncodeBHist P,
        effectiveCauchySequenceEncodeBHist N]

private def effectiveCauchySequenceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveCauchySequenceEventAt index rest

def effectiveCauchySequenceFromEventFlow : EventFlow → Option EffectiveCauchySequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (EffectiveCauchySequenceUp.mk
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 0 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 1 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 2 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 3 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 4 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 5 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 6 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 7 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 8 ef))
          (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEventAt 9 ef)))

private theorem effectiveCauchySequence_round_trip :
    ∀ x : EffectiveCauchySequenceUp,
      effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M W D Q E H C P N =>
      change
        some
          (EffectiveCauchySequenceUp.mk
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist S))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist M))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist W))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist D))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist Q))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist E))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist H))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist C))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist P))
            (effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist N))) =
          some (EffectiveCauchySequenceUp.mk S M W D Q E H C P N)
      rw [effectiveCauchySequence_decode_encode_bhist S,
        effectiveCauchySequence_decode_encode_bhist M,
        effectiveCauchySequence_decode_encode_bhist W,
        effectiveCauchySequence_decode_encode_bhist D,
        effectiveCauchySequence_decode_encode_bhist Q,
        effectiveCauchySequence_decode_encode_bhist E,
        effectiveCauchySequence_decode_encode_bhist H,
        effectiveCauchySequence_decode_encode_bhist C,
        effectiveCauchySequence_decode_encode_bhist P,
        effectiveCauchySequence_decode_encode_bhist N]

private theorem effectiveCauchySequenceToEventFlow_injective
    {x y : EffectiveCauchySequenceUp} :
    effectiveCauchySequenceToEventFlow x = effectiveCauchySequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow x) =
        effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow y) :=
    congrArg effectiveCauchySequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveCauchySequence_round_trip x).symm
      (Eq.trans hread (effectiveCauchySequence_round_trip y)))

instance effectiveCauchySequenceBHistCarrier : BHistCarrier EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchySequenceToEventFlow
  fromEventFlow := effectiveCauchySequenceFromEventFlow

instance effectiveCauchySequenceChapterTasteGate :
    ChapterTasteGate EffectiveCauchySequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow x) = some x
    exact effectiveCauchySequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveCauchySequenceToEventFlow_injective heq)

theorem EffectiveCauchySequenceUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      effectiveCauchySequenceDecodeBHist (effectiveCauchySequenceEncodeBHist h) = h) ∧
      (∀ x : EffectiveCauchySequenceUp,
        effectiveCauchySequenceFromEventFlow (effectiveCauchySequenceToEventFlow x) = some x) ∧
      (∀ x y : EffectiveCauchySequenceUp,
        effectiveCauchySequenceToEventFlow x = effectiveCauchySequenceToEventFlow y → x = y) ∧
      effectiveCauchySequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨effectiveCauchySequence_decode_encode_bhist, effectiveCauchySequence_round_trip,
    fun _ _ heq => effectiveCauchySequenceToEventFlow_injective heq, rfl⟩

end BEDC.Derived.EffectiveCauchySequenceUp.TasteGate
