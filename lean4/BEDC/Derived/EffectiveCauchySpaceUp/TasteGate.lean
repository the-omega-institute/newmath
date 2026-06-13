import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveCauchySpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveCauchySpaceUp : Type where
  | mk : (A M E S R D L U H C P N : BHist) → EffectiveCauchySpaceUp
  deriving DecidableEq

def effectiveCauchySpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveCauchySpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveCauchySpaceEncodeBHist h

def effectiveCauchySpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveCauchySpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveCauchySpaceDecodeBHist tail)

private theorem effectiveCauchySpaceDecode_encode_bhist :
    ∀ h : BHist,
      effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveCauchySpaceFields : EffectiveCauchySpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveCauchySpaceUp.mk A M E S R D L U H C P N =>
      [A, M, E, S, R, D, L, U, H, C, P, N]

def effectiveCauchySpaceToEventFlow : EffectiveCauchySpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (effectiveCauchySpaceFields x).map effectiveCauchySpaceEncodeBHist

private def effectiveCauchySpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveCauchySpaceEventAtDefault index rest

def effectiveCauchySpaceFromEventFlow : EventFlow → Option EffectiveCauchySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EffectiveCauchySpaceUp.mk
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 0 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 1 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 2 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 3 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 4 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 5 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 6 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 7 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 8 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 9 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 10 ef))
        (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEventAtDefault 11 ef)))

private theorem effectiveCauchySpace_round_trip :
    ∀ x : EffectiveCauchySpaceUp,
      effectiveCauchySpaceFromEventFlow (effectiveCauchySpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A M E S R D L U H C P N =>
      change
        some
          (EffectiveCauchySpaceUp.mk
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist A))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist M))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist E))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist S))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist R))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist D))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist L))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist U))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist H))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist C))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist P))
            (effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist N))) =
          some (EffectiveCauchySpaceUp.mk A M E S R D L U H C P N)
      rw [effectiveCauchySpaceDecode_encode_bhist A, effectiveCauchySpaceDecode_encode_bhist M,
        effectiveCauchySpaceDecode_encode_bhist E, effectiveCauchySpaceDecode_encode_bhist S,
        effectiveCauchySpaceDecode_encode_bhist R, effectiveCauchySpaceDecode_encode_bhist D,
        effectiveCauchySpaceDecode_encode_bhist L, effectiveCauchySpaceDecode_encode_bhist U,
        effectiveCauchySpaceDecode_encode_bhist H, effectiveCauchySpaceDecode_encode_bhist C,
        effectiveCauchySpaceDecode_encode_bhist P, effectiveCauchySpaceDecode_encode_bhist N]

private theorem effectiveCauchySpaceToEventFlow_injective
    {x y : EffectiveCauchySpaceUp} :
    effectiveCauchySpaceToEventFlow x = effectiveCauchySpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveCauchySpaceFromEventFlow (effectiveCauchySpaceToEventFlow x) =
        effectiveCauchySpaceFromEventFlow (effectiveCauchySpaceToEventFlow y) :=
    congrArg effectiveCauchySpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (effectiveCauchySpace_round_trip x).symm
      (Eq.trans hread (effectiveCauchySpace_round_trip y)))

instance effectiveCauchySpaceBHistCarrier : BHistCarrier EffectiveCauchySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveCauchySpaceToEventFlow
  fromEventFlow := effectiveCauchySpaceFromEventFlow

instance effectiveCauchySpaceChapterTasteGate : ChapterTasteGate EffectiveCauchySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveCauchySpaceFromEventFlow (effectiveCauchySpaceToEventFlow x) = some x
    exact effectiveCauchySpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (effectiveCauchySpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate EffectiveCauchySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveCauchySpaceChapterTasteGate

theorem EffectiveCauchySpaceTasteGate_single_carrier_alignment :
    effectiveCauchySpaceEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      (∀ h : BHist,
        effectiveCauchySpaceDecodeBHist (effectiveCauchySpaceEncodeBHist h) = h) ∧
        ChapterTasteGate EffectiveCauchySpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨rfl, effectiveCauchySpaceDecode_encode_bhist, effectiveCauchySpaceChapterTasteGate⟩

end BEDC.Derived.EffectiveCauchySpaceUp
