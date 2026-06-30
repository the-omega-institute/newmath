import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactEquicontinuousFamilyModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactEquicontinuousFamilyModulusUp : Type where
  | mk (X F M U W R S H C P N : BHist) : CompactEquicontinuousFamilyModulusUp
  deriving DecidableEq

def compactEquicontinuousFamilyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactEquicontinuousFamilyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactEquicontinuousFamilyModulusEncodeBHist h

def compactEquicontinuousFamilyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactEquicontinuousFamilyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactEquicontinuousFamilyModulusDecodeBHist tail)

private theorem CompactEquicontinuousFamilyModulusTasteGate_decode_encode :
    ∀ h : BHist,
      compactEquicontinuousFamilyModulusDecodeBHist
          (compactEquicontinuousFamilyModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactEquicontinuousFamilyModulusFields :
    CompactEquicontinuousFamilyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactEquicontinuousFamilyModulusUp.mk X F M U W R S H C P N =>
      [X, F, M, U, W, R, S, H, C, P, N]

def compactEquicontinuousFamilyModulusToEventFlow :
    CompactEquicontinuousFamilyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactEquicontinuousFamilyModulusFields x).map
        compactEquicontinuousFamilyModulusEncodeBHist

private def compactEquicontinuousFamilyModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactEquicontinuousFamilyModulusEventAtDefault index rest

def compactEquicontinuousFamilyModulusFromEventFlow
    (ef : EventFlow) : Option CompactEquicontinuousFamilyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactEquicontinuousFamilyModulusUp.mk
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 0 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 1 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 2 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 3 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 4 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 5 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 6 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 7 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 8 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 9 ef))
      (compactEquicontinuousFamilyModulusDecodeBHist
        (compactEquicontinuousFamilyModulusEventAtDefault 10 ef)))

private theorem CompactEquicontinuousFamilyModulusTasteGate_round_trip :
    ∀ x : CompactEquicontinuousFamilyModulusUp,
      compactEquicontinuousFamilyModulusFromEventFlow
          (compactEquicontinuousFamilyModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F M U W R S H C P N =>
      change
        some
          (CompactEquicontinuousFamilyModulusUp.mk
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist X))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist F))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist M))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist U))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist W))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist R))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist S))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist H))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist C))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist P))
            (compactEquicontinuousFamilyModulusDecodeBHist
              (compactEquicontinuousFamilyModulusEncodeBHist N))) =
          some (CompactEquicontinuousFamilyModulusUp.mk X F M U W R S H C P N)
      rw [CompactEquicontinuousFamilyModulusTasteGate_decode_encode X,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode F,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode M,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode U,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode W,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode R,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode S,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode H,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode C,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode P,
        CompactEquicontinuousFamilyModulusTasteGate_decode_encode N]

private theorem CompactEquicontinuousFamilyModulusTasteGate_toEventFlow_injective
    {x y : CompactEquicontinuousFamilyModulusUp} :
    compactEquicontinuousFamilyModulusToEventFlow x =
      compactEquicontinuousFamilyModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactEquicontinuousFamilyModulusFromEventFlow
          (compactEquicontinuousFamilyModulusToEventFlow x) =
        compactEquicontinuousFamilyModulusFromEventFlow
          (compactEquicontinuousFamilyModulusToEventFlow y) :=
    congrArg compactEquicontinuousFamilyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompactEquicontinuousFamilyModulusTasteGate_round_trip x).symm
      (Eq.trans hread (CompactEquicontinuousFamilyModulusTasteGate_round_trip y)))

instance compactEquicontinuousFamilyModulusBHistCarrier :
    BHistCarrier CompactEquicontinuousFamilyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactEquicontinuousFamilyModulusToEventFlow
  fromEventFlow := compactEquicontinuousFamilyModulusFromEventFlow

instance compactEquicontinuousFamilyModulusChapterTasteGate :
    ChapterTasteGate CompactEquicontinuousFamilyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactEquicontinuousFamilyModulusFromEventFlow
          (compactEquicontinuousFamilyModulusToEventFlow x) =
        some x
    exact CompactEquicontinuousFamilyModulusTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactEquicontinuousFamilyModulusTasteGate_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CompactEquicontinuousFamilyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactEquicontinuousFamilyModulusChapterTasteGate

theorem CompactEquicontinuousFamilyModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactEquicontinuousFamilyModulusDecodeBHist
          (compactEquicontinuousFamilyModulusEncodeBHist h) =
        h) ∧
      (∀ x : CompactEquicontinuousFamilyModulusUp,
        compactEquicontinuousFamilyModulusFromEventFlow
            (compactEquicontinuousFamilyModulusToEventFlow x) =
          some x) ∧
        (∀ x y : CompactEquicontinuousFamilyModulusUp,
          compactEquicontinuousFamilyModulusToEventFlow x =
            compactEquicontinuousFamilyModulusToEventFlow y → x = y) ∧
          compactEquicontinuousFamilyModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactEquicontinuousFamilyModulusTasteGate_decode_encode,
      CompactEquicontinuousFamilyModulusTasteGate_round_trip,
      (fun _ _ heq => CompactEquicontinuousFamilyModulusTasteGate_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompactEquicontinuousFamilyModulusUp.TasteGate
