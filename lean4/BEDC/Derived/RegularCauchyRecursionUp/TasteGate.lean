import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRecursionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRecursionUp : Type where
  | mk (Q S D E L H C P N : BHist) : RegularCauchyRecursionUp
  deriving DecidableEq

def regularCauchyRecursionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRecursionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRecursionEncodeBHist h

def regularCauchyRecursionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRecursionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRecursionDecodeBHist tail)

private theorem RegularCauchyRecursionTasteGate_decode_encode :
    ∀ h : BHist,
      regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyRecursionFields : RegularCauchyRecursionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRecursionUp.mk Q S D E L H C P N => [Q, S, D, E, L, H, C, P, N]

def regularCauchyRecursionToEventFlow : RegularCauchyRecursionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyRecursionFields x).map regularCauchyRecursionEncodeBHist

def regularCauchyRecursionFromEventFlow : EventFlow → Option RegularCauchyRecursionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [Q, S, D, E, L, H, C, P, N] =>
      some
        (RegularCauchyRecursionUp.mk
          (regularCauchyRecursionDecodeBHist Q)
          (regularCauchyRecursionDecodeBHist S)
          (regularCauchyRecursionDecodeBHist D)
          (regularCauchyRecursionDecodeBHist E)
          (regularCauchyRecursionDecodeBHist L)
          (regularCauchyRecursionDecodeBHist H)
          (regularCauchyRecursionDecodeBHist C)
          (regularCauchyRecursionDecodeBHist P)
          (regularCauchyRecursionDecodeBHist N))
  | _ => none

private theorem RegularCauchyRecursionTasteGate_round_trip :
    ∀ x : RegularCauchyRecursionUp,
      regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S D E L H C P N =>
      change
        some
          (RegularCauchyRecursionUp.mk
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist Q))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist S))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist D))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist E))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist L))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist H))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist C))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist P))
            (regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist N))) =
          some (RegularCauchyRecursionUp.mk Q S D E L H C P N)
      rw [RegularCauchyRecursionTasteGate_decode_encode Q,
        RegularCauchyRecursionTasteGate_decode_encode S,
        RegularCauchyRecursionTasteGate_decode_encode D,
        RegularCauchyRecursionTasteGate_decode_encode E,
        RegularCauchyRecursionTasteGate_decode_encode L,
        RegularCauchyRecursionTasteGate_decode_encode H,
        RegularCauchyRecursionTasteGate_decode_encode C,
        RegularCauchyRecursionTasteGate_decode_encode P,
        RegularCauchyRecursionTasteGate_decode_encode N]

private theorem RegularCauchyRecursionTasteGate_toEventFlow_injective
    {x y : RegularCauchyRecursionUp} :
    regularCauchyRecursionToEventFlow x = regularCauchyRecursionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow x) =
        regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow y) :=
    congrArg regularCauchyRecursionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyRecursionTasteGate_round_trip x).symm
      (Eq.trans hread (RegularCauchyRecursionTasteGate_round_trip y)))

instance regularCauchyRecursionBHistCarrier : BHistCarrier RegularCauchyRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRecursionToEventFlow
  fromEventFlow := regularCauchyRecursionFromEventFlow

instance regularCauchyRecursionChapterTasteGate : ChapterTasteGate RegularCauchyRecursionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow x) = some x
    exact RegularCauchyRecursionTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyRecursionTasteGate_toEventFlow_injective heq)

theorem RegularCauchyRecursionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyRecursionDecodeBHist (regularCauchyRecursionEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyRecursionUp,
        regularCauchyRecursionFromEventFlow (regularCauchyRecursionToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyRecursionUp,
        regularCauchyRecursionToEventFlow x = regularCauchyRecursionToEventFlow y → x = y) ∧
      regularCauchyRecursionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyRecursionTasteGate_decode_encode
  constructor
  · exact RegularCauchyRecursionTasteGate_round_trip
  constructor
  · intro x y heq
    exact RegularCauchyRecursionTasteGate_toEventFlow_injective heq
  · rfl

end BEDC.Derived.RegularCauchyRecursionUp
