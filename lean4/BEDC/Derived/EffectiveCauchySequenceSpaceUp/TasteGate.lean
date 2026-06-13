import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchySequenceSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveCauchySequenceSpaceUp : Type where
  | mk (S R D Q A T K H C P N : BHist) : EffectiveCauchySequenceSpaceUp
  deriving DecidableEq

def effectiveCauchySequenceSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchySequenceSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchySequenceSpaceEncodeBHist h

def effectiveCauchySequenceSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchySequenceSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchySequenceSpaceDecodeBHist tail)

private theorem EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      effectiveCauchySequenceSpaceDecodeBHist
        (effectiveCauchySequenceSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchySequenceSpaceFields :
    EffectiveCauchySequenceSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchySequenceSpaceUp.mk S R D Q A T K H C P N =>
      [S, R, D, Q, A, T, K, H, C, P, N]

def effectiveCauchySequenceSpaceToEventFlow :
    EffectiveCauchySequenceSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (effectiveCauchySequenceSpaceFields x).map effectiveCauchySequenceSpaceEncodeBHist

private def effectiveCauchySequenceSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveCauchySequenceSpaceEventAt index rest

def effectiveCauchySequenceSpaceFromEventFlow
    (ef : EventFlow) : Option EffectiveCauchySequenceSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EffectiveCauchySequenceSpaceUp.mk
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 0 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 1 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 2 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 3 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 4 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 5 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 6 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 7 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 8 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 9 ef))
      (effectiveCauchySequenceSpaceDecodeBHist (effectiveCauchySequenceSpaceEventAt 10 ef)))

private theorem EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip
    (x : EffectiveCauchySequenceSpaceUp) :
    effectiveCauchySequenceSpaceFromEventFlow
      (effectiveCauchySequenceSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S R D Q A T K H C P N =>
      change
        some
          (EffectiveCauchySequenceSpaceUp.mk
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist S))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist R))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist D))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist Q))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist A))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist T))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist K))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist H))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist C))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist P))
            (effectiveCauchySequenceSpaceDecodeBHist
              (effectiveCauchySequenceSpaceEncodeBHist N))) =
          some (EffectiveCauchySequenceSpaceUp.mk S R D Q A T K H C P N)
      rw [EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode S,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode R,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode D,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode A,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode T,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode K,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode H,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode C,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode P,
        EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem EffectiveCauchySequenceSpaceToEventFlow_injective
    {x y : EffectiveCauchySequenceSpaceUp} :
    effectiveCauchySequenceSpaceToEventFlow x =
      effectiveCauchySequenceSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchySequenceSpaceFromEventFlow
          (effectiveCauchySequenceSpaceToEventFlow x) =
        effectiveCauchySequenceSpaceFromEventFlow
          (effectiveCauchySequenceSpaceToEventFlow y) :=
    congrArg effectiveCauchySequenceSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance effectiveCauchySequenceSpaceBHistCarrier :
    BHistCarrier EffectiveCauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchySequenceSpaceToEventFlow
  fromEventFlow := effectiveCauchySequenceSpaceFromEventFlow

instance effectiveCauchySequenceSpaceChapterTasteGate :
    ChapterTasteGate EffectiveCauchySequenceSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      effectiveCauchySequenceSpaceFromEventFlow
        (effectiveCauchySequenceSpaceToEventFlow x) = some x
    exact EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EffectiveCauchySequenceSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate EffectiveCauchySequenceSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveCauchySequenceSpaceChapterTasteGate

theorem EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      effectiveCauchySequenceSpaceDecodeBHist
        (effectiveCauchySequenceSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EffectiveCauchySequenceSpaceUp) ∧
        Nonempty (ChapterTasteGate EffectiveCauchySequenceSpaceUp) ∧
          effectiveCauchySequenceSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EffectiveCauchySequenceSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨effectiveCauchySequenceSpaceBHistCarrier⟩,
      ⟨effectiveCauchySequenceSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.EffectiveCauchySequenceSpaceUp
