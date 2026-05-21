import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCompletionModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCompletionModulusUp : Type where
  | mk (M S n k W D R E H C P N : BHist) : BishopCompletionModulusUp
  deriving DecidableEq

def bishopCompletionModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCompletionModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCompletionModulusEncodeBHist h

def bishopCompletionModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCompletionModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCompletionModulusDecodeBHist tail)

private theorem BishopCompletionModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCompletionModulusFields : BishopCompletionModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCompletionModulusUp.mk M S n k W D R E H C P N =>
      [M, S, n, k, W, D, R, E, H, C, P, N]

def bishopCompletionModulusToEventFlow : BishopCompletionModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map bishopCompletionModulusEncodeBHist (bishopCompletionModulusFields x)

private def bishopCompletionModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCompletionModulusEventAt index rest

def bishopCompletionModulusFromEventFlow : EventFlow → Option BishopCompletionModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BishopCompletionModulusUp.mk
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 0 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 1 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 2 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 3 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 4 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 5 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 6 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 7 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 8 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 9 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 10 ef))
          (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEventAt 11 ef)))

private theorem BishopCompletionModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCompletionModulusUp,
      bishopCompletionModulusFromEventFlow (bishopCompletionModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S n k W D R E H C P N =>
      change
        some
          (BishopCompletionModulusUp.mk
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist M))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist S))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist n))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist k))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist W))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist D))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist R))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist E))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist H))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist C))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist P))
            (bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist N))) =
          some (BishopCompletionModulusUp.mk M S n k W D R E H C P N)
      rw [BishopCompletionModulusTasteGate_single_carrier_alignment_decode M,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode S,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode n,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode k,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode W,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode D,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode R,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode E,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode H,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode C,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode P,
        BishopCompletionModulusTasteGate_single_carrier_alignment_decode N]

private theorem BishopCompletionModulusTasteGate_single_carrier_alignment_injective
    {x y : BishopCompletionModulusUp} :
    bishopCompletionModulusToEventFlow x = bishopCompletionModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCompletionModulusFromEventFlow (bishopCompletionModulusToEventFlow x) =
        bishopCompletionModulusFromEventFlow (bishopCompletionModulusToEventFlow y) :=
    congrArg bishopCompletionModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopCompletionModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCompletionModulusTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopCompletionModulusTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopCompletionModulusUp,
      bishopCompletionModulusFields x = bishopCompletionModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 S1 n1 k1 W1 D1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 S2 n2 k2 W2 D2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopCompletionModulusBHistCarrier : BHistCarrier BishopCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCompletionModulusToEventFlow
  fromEventFlow := bishopCompletionModulusFromEventFlow

instance bishopCompletionModulusChapterTasteGate :
    ChapterTasteGate BishopCompletionModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCompletionModulusFromEventFlow (bishopCompletionModulusToEventFlow x) = some x
    exact BishopCompletionModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopCompletionModulusTasteGate_single_carrier_alignment_injective heq)

theorem BishopCompletionModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCompletionModulusDecodeBHist (bishopCompletionModulusEncodeBHist h) = h) ∧
      (∀ x : BishopCompletionModulusUp,
        bishopCompletionModulusFromEventFlow (bishopCompletionModulusToEventFlow x) = some x) ∧
        (∀ x y : BishopCompletionModulusUp,
          bishopCompletionModulusToEventFlow x = bishopCompletionModulusToEventFlow y →
            x = y) ∧
          bishopCompletionModulusEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : BishopCompletionModulusUp,
              bishopCompletionModulusFields x = bishopCompletionModulusFields y → x = y) ∧
              (∃ x y : BishopCompletionModulusUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact BishopCompletionModulusTasteGate_single_carrier_alignment_decode
  · constructor
    · exact BishopCompletionModulusTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact BishopCompletionModulusTasteGate_single_carrier_alignment_injective heq
      · constructor
        · rfl
        · constructor
          · exact BishopCompletionModulusTasteGate_single_carrier_alignment_fields
          · exact
              Exists.intro
                (BishopCompletionModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty)
                (Exists.intro
                  (BishopCompletionModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty)
                  (by
                    intro h
                    cases h))

end BEDC.Derived.BishopCompletionModulusUp
