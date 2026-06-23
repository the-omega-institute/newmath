import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealDiagonalModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealDiagonalModulusUp : Type where
  | mk (n mu S R D E H C Q N : BHist) : RealDiagonalModulusUp
  deriving DecidableEq

def realDiagonalModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realDiagonalModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realDiagonalModulusEncodeBHist h

def realDiagonalModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realDiagonalModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realDiagonalModulusDecodeBHist tail)

private theorem RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realDiagonalModulusFields : RealDiagonalModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealDiagonalModulusUp.mk n mu S R D E H C Q N => [n, mu, S, R, D, E, H, C, Q, N]

def realDiagonalModulusToEventFlow : RealDiagonalModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realDiagonalModulusFields x).map realDiagonalModulusEncodeBHist

private def realDiagonalModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realDiagonalModulusEventAt index rest

def realDiagonalModulusFromEventFlow (ef : EventFlow) : Option RealDiagonalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealDiagonalModulusUp.mk
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 0 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 1 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 2 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 3 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 4 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 5 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 6 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 7 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 8 ef))
      (realDiagonalModulusDecodeBHist (realDiagonalModulusEventAt 9 ef)))

private theorem RealDiagonalModulusTasteGate_single_carrier_alignment_round_trip
    (x : RealDiagonalModulusUp) :
    realDiagonalModulusFromEventFlow (realDiagonalModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk n mu S R D E H C Q N =>
      change
        some
          (RealDiagonalModulusUp.mk
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist n))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist mu))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist S))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist R))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist D))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist E))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist H))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist C))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist Q))
            (realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist N))) =
          some (RealDiagonalModulusUp.mk n mu S R D E H C Q N)
      rw [RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode n,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode mu,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode S,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode R,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode D,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode E,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode H,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode C,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode Q,
        RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealDiagonalModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealDiagonalModulusUp} :
    realDiagonalModulusToEventFlow x = realDiagonalModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realDiagonalModulusFromEventFlow (realDiagonalModulusToEventFlow x) =
        realDiagonalModulusFromEventFlow (realDiagonalModulusToEventFlow y) :=
    congrArg realDiagonalModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealDiagonalModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealDiagonalModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealDiagonalModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealDiagonalModulusUp, realDiagonalModulusFields x = realDiagonalModulusFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk n₁ mu₁ S₁ R₁ D₁ E₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk n₂ mu₂ S₂ R₂ D₂ E₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance realDiagonalModulusBHistCarrier : BHistCarrier RealDiagonalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realDiagonalModulusToEventFlow
  fromEventFlow := realDiagonalModulusFromEventFlow

instance realDiagonalModulusChapterTasteGate : ChapterTasteGate RealDiagonalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realDiagonalModulusFromEventFlow (realDiagonalModulusToEventFlow x) = some x
    exact RealDiagonalModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealDiagonalModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realDiagonalModulusFieldFaithful : FieldFaithful RealDiagonalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realDiagonalModulusFields
  field_faithful := RealDiagonalModulusTasteGate_single_carrier_alignment_fields

instance realDiagonalModulusNontrivial : Nontrivial RealDiagonalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealDiagonalModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealDiagonalModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RealDiagonalModulusTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RealDiagonalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realDiagonalModulusChapterTasteGate

theorem RealDiagonalModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, realDiagonalModulusDecodeBHist (realDiagonalModulusEncodeBHist h) = h) ∧
      (∀ x : RealDiagonalModulusUp,
        realDiagonalModulusFromEventFlow (realDiagonalModulusToEventFlow x) = some x) ∧
        (∀ x y : RealDiagonalModulusUp,
          realDiagonalModulusToEventFlow x = realDiagonalModulusToEventFlow y → x = y) ∧
          realDiagonalModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealDiagonalModulusTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact RealDiagonalModulusTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RealDiagonalModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.RealDiagonalModulusUp
