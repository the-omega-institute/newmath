import BEDC.Derived.EffectiveModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EffectiveModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EffectiveModulusUp : Type where
  | mk (R S D u L H C P N : BHist) : EffectiveModulusUp
  deriving DecidableEq

def effectiveModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: effectiveModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: effectiveModulusEncodeBHist h

def effectiveModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (effectiveModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (effectiveModulusDecodeBHist tail)

private theorem EffectiveModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, effectiveModulusDecodeBHist (effectiveModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def effectiveModulusFields : EffectiveModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EffectiveModulusUp.mk R S D u L H C P N => [R, S, D, u, L, H, C, P, N]

def effectiveModulusToEventFlow : EffectiveModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (effectiveModulusFields x).map effectiveModulusEncodeBHist

private def effectiveModulusRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => effectiveModulusRawAt index rest

private def effectiveModulusLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => effectiveModulusLengthEq index rest

def effectiveModulusFromEventFlow : EventFlow → Option EffectiveModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match effectiveModulusLengthEq 9 flow with
      | true =>
          some
            (EffectiveModulusUp.mk
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 0 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 1 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 2 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 3 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 4 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 5 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 6 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 7 flow))
              (effectiveModulusDecodeBHist (effectiveModulusRawAt 8 flow)))
      | false => none

private theorem EffectiveModulusTasteGate_single_carrier_alignment_round_trip
    (x : EffectiveModulusUp) :
    effectiveModulusFromEventFlow (effectiveModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R S D u L H C P N =>
      change
        some
          (EffectiveModulusUp.mk
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist R))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist S))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist D))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist u))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist L))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist H))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist C))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist P))
            (effectiveModulusDecodeBHist (effectiveModulusEncodeBHist N))) =
          some (EffectiveModulusUp.mk R S D u L H C P N)
      rw [EffectiveModulusTasteGate_single_carrier_alignment_decode_encode R,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode S,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode D,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode u,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode L,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode H,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode C,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode P,
        EffectiveModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem EffectiveModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EffectiveModulusUp} :
    effectiveModulusToEventFlow x = effectiveModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      effectiveModulusFromEventFlow (effectiveModulusToEventFlow x) =
        effectiveModulusFromEventFlow (effectiveModulusToEventFlow y) :=
    congrArg effectiveModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EffectiveModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EffectiveModulusTasteGate_single_carrier_alignment_round_trip y)))

instance effectiveModulusBHistCarrier : BHistCarrier EffectiveModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := effectiveModulusToEventFlow
  fromEventFlow := effectiveModulusFromEventFlow

instance effectiveModulusChapterTasteGate : ChapterTasteGate EffectiveModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change effectiveModulusFromEventFlow (effectiveModulusToEventFlow x) = some x
    exact EffectiveModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EffectiveModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def EffectiveModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate EffectiveModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  effectiveModulusChapterTasteGate

theorem EffectiveModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, effectiveModulusDecodeBHist (effectiveModulusEncodeBHist h) = h) ∧
      (∀ x : EffectiveModulusUp,
        effectiveModulusFromEventFlow (effectiveModulusToEventFlow x) = some x) ∧
        (∀ x y : EffectiveModulusUp,
          effectiveModulusToEventFlow x = effectiveModulusToEventFlow y → x = y) ∧
          effectiveModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨EffectiveModulusTasteGate_single_carrier_alignment_decode_encode,
      EffectiveModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        EffectiveModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EffectiveModulusUp
