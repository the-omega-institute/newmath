import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailModulusUp : Type where
  | mk (S Q T W D H C P N : BHist) : RegularCauchyTailModulusUp
  deriving DecidableEq

def regularCauchyTailModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailModulusEncodeBHist h

def regularCauchyTailModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailModulusDecodeBHist tail)

private theorem RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailModulusFields : RegularCauchyTailModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailModulusUp.mk S Q T W D H C P N => [S, Q, T, W, D, H, C, P, N]

def regularCauchyTailModulusToEventFlow : RegularCauchyTailModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailModulusFields x).map regularCauchyTailModulusEncodeBHist

private def regularCauchyTailModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailModulusEventAt index rest

def regularCauchyTailModulusFromEventFlow (ef : EventFlow) :
    Option RegularCauchyTailModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailModulusUp.mk
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 0 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 1 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 2 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 3 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 4 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 5 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 6 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 7 ef))
      (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEventAt 8 ef)))

private theorem RegularCauchyTailModulusTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyTailModulusUp) :
    regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S Q T W D H C P N =>
      change
        some
          (RegularCauchyTailModulusUp.mk
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist S))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist Q))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist T))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist W))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist D))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist H))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist C))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist P))
            (regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist N))) =
          some (RegularCauchyTailModulusUp.mk S Q T W D H C P N)
      rw [RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTailModulusUp} :
    regularCauchyTailModulusToEventFlow x = regularCauchyTailModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow x) =
        regularCauchyTailModulusFromEventFlow (regularCauchyTailModulusToEventFlow y) :=
    congrArg regularCauchyTailModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyTailModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTailModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyTailModulusTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyTailModulusUp,
      regularCauchyTailModulusFields x = regularCauchyTailModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ Q₁ T₁ W₁ D₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ T₂ W₂ D₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyTailModulusBHistCarrier :
    BHistCarrier RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailModulusToEventFlow
  fromEventFlow := regularCauchyTailModulusFromEventFlow

instance regularCauchyTailModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailModulusFromEventFlow
        (regularCauchyTailModulusToEventFlow x) = some x
    exact RegularCauchyTailModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyTailModulusFieldFaithful :
    FieldFaithful RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailModulusFields
  field_faithful := RegularCauchyTailModulusTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyTailModulusNontrivial : Nontrivial RegularCauchyTailModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchyTailModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyTailModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailModulusChapterTasteGate

theorem RegularCauchyTailModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailModulusDecodeBHist (regularCauchyTailModulusEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailModulusUp,
        regularCauchyTailModulusFromEventFlow
          (regularCauchyTailModulusToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailModulusUp,
          regularCauchyTailModulusToEventFlow x =
              regularCauchyTailModulusToEventFlow y →
            x = y) ∧
          regularCauchyTailModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyTailModulusTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyTailModulusTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyTailModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyTailModulusUp
