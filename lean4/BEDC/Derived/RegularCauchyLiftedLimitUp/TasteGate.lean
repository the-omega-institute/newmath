import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLiftedLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLiftedLimitUp : Type where
  | mk (D S R W E H C P N : BHist) : RegularCauchyLiftedLimitUp
  deriving DecidableEq

def regularCauchyLiftedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLiftedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLiftedLimitEncodeBHist h

def regularCauchyLiftedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLiftedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLiftedLimitDecodeBHist tail)

private theorem RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyLiftedLimitDecodeBHist
        (regularCauchyLiftedLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLiftedLimitFields : RegularCauchyLiftedLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLiftedLimitUp.mk D S R W E H C P N => [D, S, R, W, E, H, C, P, N]

def regularCauchyLiftedLimitToEventFlow : RegularCauchyLiftedLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyLiftedLimitFields x).map regularCauchyLiftedLimitEncodeBHist

private def regularCauchyLiftedLimitEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLiftedLimitEventAtDefault index rest

def regularCauchyLiftedLimitFromEventFlow
    (ef : EventFlow) : Option RegularCauchyLiftedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLiftedLimitUp.mk
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 0 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 1 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 2 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 3 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 4 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 5 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 6 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 7 ef))
      (regularCauchyLiftedLimitDecodeBHist (regularCauchyLiftedLimitEventAtDefault 8 ef)))

private theorem RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyLiftedLimitUp,
      regularCauchyLiftedLimitFromEventFlow
        (regularCauchyLiftedLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R W E H C P N =>
      change
        some
          (RegularCauchyLiftedLimitUp.mk
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist D))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist S))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist R))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist W))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist E))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist H))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist C))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist P))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist N))) =
          some (RegularCauchyLiftedLimitUp.mk D S R W E H C P N)
      rw [RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode D,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode S,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode R,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode W,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode E,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode H,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode C,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode P,
        RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyLiftedLimitUp} :
    regularCauchyLiftedLimitToEventFlow x =
      regularCauchyLiftedLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLiftedLimitFromEventFlow
          (regularCauchyLiftedLimitToEventFlow x) =
        regularCauchyLiftedLimitFromEventFlow
          (regularCauchyLiftedLimitToEventFlow y) :=
    congrArg regularCauchyLiftedLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyLiftedLimitBHistCarrier :
    BHistCarrier RegularCauchyLiftedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLiftedLimitToEventFlow
  fromEventFlow := regularCauchyLiftedLimitFromEventFlow

instance regularCauchyLiftedLimitChapterTasteGate :
    ChapterTasteGate RegularCauchyLiftedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLiftedLimitFromEventFlow
        (regularCauchyLiftedLimitToEventFlow x) = some x
    exact RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyLiftedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLiftedLimitChapterTasteGate

theorem RegularCauchyLiftedLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLiftedLimitDecodeBHist
        (regularCauchyLiftedLimitEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyLiftedLimitUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyLiftedLimitUp) ∧
          regularCauchyLiftedLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  constructor
  · exact RegularCauchyLiftedLimitTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨regularCauchyLiftedLimitBHistCarrier⟩
    · constructor
      · exact ⟨regularCauchyLiftedLimitChapterTasteGate⟩
      · rfl

end BEDC.Derived.RegularCauchyLiftedLimitUp
