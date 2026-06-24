import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactOscillationBarModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactOscillationBarModulusUp : Type where
  | mk : (K F D R B U H C P N : BHist) → CompactOscillationBarModulusUp
  deriving DecidableEq

def compactOscillationBarModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactOscillationBarModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactOscillationBarModulusEncodeBHist h

def compactOscillationBarModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactOscillationBarModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactOscillationBarModulusDecodeBHist tail)

private theorem compactOscillationBarModulusDecode_encode_bhist :
    ∀ h : BHist,
      compactOscillationBarModulusDecodeBHist
          (compactOscillationBarModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactOscillationBarModulusFields :
    CompactOscillationBarModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactOscillationBarModulusUp.mk K F D R B U H C P N =>
      [K, F, D, R, B, U, H, C, P, N]

def compactOscillationBarModulusToEventFlow :
    CompactOscillationBarModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactOscillationBarModulusFields x).map
        compactOscillationBarModulusEncodeBHist

private def compactOscillationBarModulusEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactOscillationBarModulusEventAtDefault index rest

def compactOscillationBarModulusFromEventFlow
    (ef : EventFlow) : Option CompactOscillationBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactOscillationBarModulusUp.mk
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 0 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 1 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 2 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 3 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 4 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 5 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 6 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 7 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 8 ef))
      (compactOscillationBarModulusDecodeBHist
        (compactOscillationBarModulusEventAtDefault 9 ef)))

private theorem compactOscillationBarModulus_round_trip :
    ∀ x : CompactOscillationBarModulusUp,
      compactOscillationBarModulusFromEventFlow
          (compactOscillationBarModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F D R B U H C P N =>
      change
        some
          (CompactOscillationBarModulusUp.mk
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist K))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist F))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist D))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist R))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist B))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist U))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist H))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist C))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist P))
            (compactOscillationBarModulusDecodeBHist
              (compactOscillationBarModulusEncodeBHist N))) =
          some (CompactOscillationBarModulusUp.mk K F D R B U H C P N)
      rw [compactOscillationBarModulusDecode_encode_bhist K,
        compactOscillationBarModulusDecode_encode_bhist F,
        compactOscillationBarModulusDecode_encode_bhist D,
        compactOscillationBarModulusDecode_encode_bhist R,
        compactOscillationBarModulusDecode_encode_bhist B,
        compactOscillationBarModulusDecode_encode_bhist U,
        compactOscillationBarModulusDecode_encode_bhist H,
        compactOscillationBarModulusDecode_encode_bhist C,
        compactOscillationBarModulusDecode_encode_bhist P,
        compactOscillationBarModulusDecode_encode_bhist N]

private theorem compactOscillationBarModulusToEventFlow_injective
    {x y : CompactOscillationBarModulusUp} :
    compactOscillationBarModulusToEventFlow x =
      compactOscillationBarModulusToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactOscillationBarModulusFromEventFlow
          (compactOscillationBarModulusToEventFlow x) =
        compactOscillationBarModulusFromEventFlow
          (compactOscillationBarModulusToEventFlow y) :=
    congrArg compactOscillationBarModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactOscillationBarModulus_round_trip x).symm
      (Eq.trans hread (compactOscillationBarModulus_round_trip y)))

instance compactOscillationBarModulusBHistCarrier :
    BHistCarrier CompactOscillationBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactOscillationBarModulusToEventFlow
  fromEventFlow := compactOscillationBarModulusFromEventFlow

instance compactOscillationBarModulusChapterTasteGate :
    ChapterTasteGate CompactOscillationBarModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactOscillationBarModulusFromEventFlow
          (compactOscillationBarModulusToEventFlow x) =
        some x
    exact compactOscillationBarModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactOscillationBarModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactOscillationBarModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactOscillationBarModulusChapterTasteGate

theorem CompactOscillationBarModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactOscillationBarModulusDecodeBHist
          (compactOscillationBarModulusEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CompactOscillationBarModulusUp) ∧
        Nonempty (ChapterTasteGate CompactOscillationBarModulusUp) ∧
          compactOscillationBarModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  constructor
  · intro h
    exact compactOscillationBarModulusDecode_encode_bhist h
  · constructor
    · exact ⟨compactOscillationBarModulusBHistCarrier⟩
    · constructor
      · exact ⟨compactOscillationBarModulusChapterTasteGate⟩
      · rfl

end BEDC.Derived.CompactOscillationBarModulusUp
