import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularSequenceModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularSequenceModulusUp : Type where
  | mk (S D Q M T H C P N : BHist) : RegularSequenceModulusUp
  deriving DecidableEq

def regularSequenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularSequenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularSequenceModulusEncodeBHist h

def regularSequenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularSequenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularSequenceModulusDecodeBHist tail)

private theorem RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularSequenceModulusFields : RegularSequenceModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularSequenceModulusUp.mk S D Q M T H C P N => [S, D, Q, M, T, H, C, P, N]

def regularSequenceModulusToEventFlow : RegularSequenceModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularSequenceModulusFields x).map regularSequenceModulusEncodeBHist

private def regularSequenceModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularSequenceModulusEventAt index rest

def regularSequenceModulusFromEventFlow (ef : EventFlow) :
    Option RegularSequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularSequenceModulusUp.mk
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 0 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 1 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 2 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 3 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 4 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 5 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 6 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 7 ef))
      (regularSequenceModulusDecodeBHist (regularSequenceModulusEventAt 8 ef)))

private theorem RegularSequenceModulusTasteGate_single_carrier_alignment_round_trip
    (x : RegularSequenceModulusUp) :
    regularSequenceModulusFromEventFlow (regularSequenceModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D Q M T H C P N =>
      change
        some
          (RegularSequenceModulusUp.mk
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist S))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist D))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist Q))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist M))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist T))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist H))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist C))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist P))
            (regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist N))) =
          some (RegularSequenceModulusUp.mk S D Q M T H C P N)
      rw [RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode S,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode D,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode Q,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode M,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode T,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode H,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode C,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode P,
        RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularSequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularSequenceModulusUp} :
    regularSequenceModulusToEventFlow x = regularSequenceModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularSequenceModulusFromEventFlow (regularSequenceModulusToEventFlow x) =
        regularSequenceModulusFromEventFlow (regularSequenceModulusToEventFlow y) :=
    congrArg regularSequenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularSequenceModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularSequenceModulusTasteGate_single_carrier_alignment_round_trip y)))

instance regularSequenceModulusBHistCarrier : BHistCarrier RegularSequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularSequenceModulusToEventFlow
  fromEventFlow := regularSequenceModulusFromEventFlow

instance regularSequenceModulusChapterTasteGate :
    ChapterTasteGate RegularSequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularSequenceModulusFromEventFlow (regularSequenceModulusToEventFlow x) = some x
    exact RegularSequenceModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularSequenceModulusTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularSequenceModulusTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier RegularSequenceModulusUp,
        Nonempty (@ChapterTasteGate RegularSequenceModulusUp carrier)) ∧
      (∀ h : BHist,
        regularSequenceModulusDecodeBHist (regularSequenceModulusEncodeBHist h) = h) ∧
        (∀ x : RegularSequenceModulusUp,
          regularSequenceModulusFromEventFlow (regularSequenceModulusToEventFlow x) = some x) ∧
          regularSequenceModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨regularSequenceModulusBHistCarrier,
        ⟨regularSequenceModulusChapterTasteGate⟩⟩,
      RegularSequenceModulusTasteGate_single_carrier_alignment_decode_encode,
      RegularSequenceModulusTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.RegularSequenceModulusUp.TasteGate
