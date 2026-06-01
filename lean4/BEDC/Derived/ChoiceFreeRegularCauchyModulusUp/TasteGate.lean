import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChoiceFreeRegularCauchyModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChoiceFreeRegularCauchyModulusUp : Type where
  | mk (D W R E K H C P N : BHist) : ChoiceFreeRegularCauchyModulusUp
  deriving DecidableEq

def choiceFreeRegularCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: choiceFreeRegularCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: choiceFreeRegularCauchyModulusEncodeBHist h

def choiceFreeRegularCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (choiceFreeRegularCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (choiceFreeRegularCauchyModulusDecodeBHist tail)

private theorem ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def choiceFreeRegularCauchyModulusToEventFlow :
    ChoiceFreeRegularCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChoiceFreeRegularCauchyModulusUp.mk D W R E K H C P N =>
      [choiceFreeRegularCauchyModulusEncodeBHist D,
        choiceFreeRegularCauchyModulusEncodeBHist W,
        choiceFreeRegularCauchyModulusEncodeBHist R,
        choiceFreeRegularCauchyModulusEncodeBHist E,
        choiceFreeRegularCauchyModulusEncodeBHist K,
        choiceFreeRegularCauchyModulusEncodeBHist H,
        choiceFreeRegularCauchyModulusEncodeBHist C,
        choiceFreeRegularCauchyModulusEncodeBHist P,
        choiceFreeRegularCauchyModulusEncodeBHist N]

private def choiceFreeRegularCauchyModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => choiceFreeRegularCauchyModulusEventAtDefault index rest

def choiceFreeRegularCauchyModulusFromEventFlow
    (ef : EventFlow) : Option ChoiceFreeRegularCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ChoiceFreeRegularCauchyModulusUp.mk
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 0 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 1 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 2 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 3 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 4 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 5 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 6 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 7 ef))
      (choiceFreeRegularCauchyModulusDecodeBHist
        (choiceFreeRegularCauchyModulusEventAtDefault 8 ef)))

private theorem ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_round_trip
    (x : ChoiceFreeRegularCauchyModulusUp) :
    choiceFreeRegularCauchyModulusFromEventFlow
      (choiceFreeRegularCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W R E K H C P N =>
      change
        some
          (ChoiceFreeRegularCauchyModulusUp.mk
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist D))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist W))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist R))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist E))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist K))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist H))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist C))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist P))
            (choiceFreeRegularCauchyModulusDecodeBHist
              (choiceFreeRegularCauchyModulusEncodeBHist N))) =
          some (ChoiceFreeRegularCauchyModulusUp.mk D W R E K H C P N)
      rw [ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode D,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode W,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode R,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode E,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode K,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode H,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode C,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode P,
        ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode N]

private theorem choiceFreeRegularCauchyModulusToEventFlow_injective
    {x y : ChoiceFreeRegularCauchyModulusUp} :
    choiceFreeRegularCauchyModulusToEventFlow x =
        choiceFreeRegularCauchyModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      choiceFreeRegularCauchyModulusFromEventFlow
          (choiceFreeRegularCauchyModulusToEventFlow x) =
        choiceFreeRegularCauchyModulusFromEventFlow
          (choiceFreeRegularCauchyModulusToEventFlow y) :=
    congrArg choiceFreeRegularCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_round_trip y)))

instance choiceFreeRegularCauchyModulusBHistCarrier :
    BHistCarrier ChoiceFreeRegularCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := choiceFreeRegularCauchyModulusToEventFlow
  fromEventFlow := choiceFreeRegularCauchyModulusFromEventFlow

instance choiceFreeRegularCauchyModulusChapterTasteGate :
    ChapterTasteGate ChoiceFreeRegularCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      choiceFreeRegularCauchyModulusFromEventFlow
        (choiceFreeRegularCauchyModulusToEventFlow x) = some x
    exact ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (choiceFreeRegularCauchyModulusToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ChoiceFreeRegularCauchyModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  choiceFreeRegularCauchyModulusChapterTasteGate

theorem ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier ChoiceFreeRegularCauchyModulusUp) ∧
      Nonempty (ChapterTasteGate ChoiceFreeRegularCauchyModulusUp) ∧
      (∀ h : BHist,
        choiceFreeRegularCauchyModulusDecodeBHist
          (choiceFreeRegularCauchyModulusEncodeBHist h) = h) ∧
      (∀ x : ChoiceFreeRegularCauchyModulusUp,
        choiceFreeRegularCauchyModulusFromEventFlow
          (choiceFreeRegularCauchyModulusToEventFlow x) = some x) ∧
      choiceFreeRegularCauchyModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨choiceFreeRegularCauchyModulusBHistCarrier⟩
  constructor
  · exact ⟨choiceFreeRegularCauchyModulusChapterTasteGate⟩
  constructor
  · exact ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_decode
  constructor
  · exact ChoiceFreeRegularCauchyModulusTasteGate_single_carrier_alignment_round_trip
  · rfl

end BEDC.Derived.ChoiceFreeRegularCauchyModulusUp
