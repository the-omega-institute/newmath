import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySequenceComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySequenceComparisonUp : Type where
  | mk (S0 S1 R0 R1 D Q E H C P N : BHist) : RegularCauchySequenceComparisonUp
  deriving DecidableEq

def regularCauchySequenceComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySequenceComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySequenceComparisonEncodeBHist h

def regularCauchySequenceComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySequenceComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySequenceComparisonDecodeBHist tail)

private theorem RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySequenceComparisonFields :
    RegularCauchySequenceComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySequenceComparisonUp.mk S0 S1 R0 R1 D Q E H C P N =>
      [S0, S1, R0, R1, D, Q, E, H, C, P, N]

def regularCauchySequenceComparisonToEventFlow :
    RegularCauchySequenceComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchySequenceComparisonFields x).map
        regularCauchySequenceComparisonEncodeBHist

private def regularCauchySequenceComparisonEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySequenceComparisonEventAt index rest

def regularCauchySequenceComparisonFromEventFlow
    (eventFlow : EventFlow) : Option RegularCauchySequenceComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchySequenceComparisonUp.mk
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 0 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 1 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 2 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 3 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 4 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 5 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 6 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 7 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 8 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 9 eventFlow))
      (regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEventAt 10 eventFlow)))

private theorem RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySequenceComparisonUp,
      regularCauchySequenceComparisonFromEventFlow
        (regularCauchySequenceComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 R0 R1 D Q E H C P N =>
      change
        some
            (RegularCauchySequenceComparisonUp.mk
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist S0))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist S1))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist R0))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist R1))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist D))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist Q))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist E))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist H))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist C))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist P))
              (regularCauchySequenceComparisonDecodeBHist
                (regularCauchySequenceComparisonEncodeBHist N))) =
          some (RegularCauchySequenceComparisonUp.mk S0 S1 R0 R1 D Q E H C P N)
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode S0]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode S1]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode R0]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode R1]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode D]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode Q]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode E]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode H]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode C]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode P]
      rw [RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySequenceComparisonUp} :
    regularCauchySequenceComparisonToEventFlow x =
        regularCauchySequenceComparisonToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySequenceComparisonFromEventFlow
          (regularCauchySequenceComparisonToEventFlow x) =
        regularCauchySequenceComparisonFromEventFlow
          (regularCauchySequenceComparisonToEventFlow y) :=
    congrArg regularCauchySequenceComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySequenceComparisonBHistCarrier :
    BHistCarrier RegularCauchySequenceComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySequenceComparisonToEventFlow
  fromEventFlow := regularCauchySequenceComparisonFromEventFlow

instance regularCauchySequenceComparisonChapterTasteGate :
    ChapterTasteGate RegularCauchySequenceComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySequenceComparisonFromEventFlow
        (regularCauchySequenceComparisonToEventFlow x) = some x
    exact RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate RegularCauchySequenceComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySequenceComparisonChapterTasteGate

theorem RegularCauchySequenceComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySequenceComparisonDecodeBHist
        (regularCauchySequenceComparisonEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySequenceComparisonUp,
        regularCauchySequenceComparisonFromEventFlow
          (regularCauchySequenceComparisonToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier RegularCauchySequenceComparisonUp) ∧
      Nonempty (ChapterTasteGate RegularCauchySequenceComparisonUp) ∧
      regularCauchySequenceComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchySequenceComparisonTasteGate_single_carrier_alignment_round_trip,
      ⟨regularCauchySequenceComparisonBHistCarrier⟩,
      ⟨regularCauchySequenceComparisonChapterTasteGate⟩, rfl⟩

end BEDC.Derived.RegularCauchySequenceComparisonUp
