import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularSequenceClusterWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularSequenceClusterWitnessUp : Type where
  | mk (S F E D R Q H C P N : BHist) : RegularSequenceClusterWitnessUp
  deriving DecidableEq

def regularSequenceClusterWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularSequenceClusterWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularSequenceClusterWitnessEncodeBHist h

def regularSequenceClusterWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularSequenceClusterWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularSequenceClusterWitnessDecodeBHist tail)

private theorem RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularSequenceClusterWitnessFields :
    RegularSequenceClusterWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularSequenceClusterWitnessUp.mk S F E D R Q H C P N =>
      [S, F, E, D, R, Q, H, C, P, N]

def regularSequenceClusterWitnessToEventFlow :
    RegularSequenceClusterWitnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularSequenceClusterWitnessFields x).map
    regularSequenceClusterWitnessEncodeBHist

private def regularSequenceClusterWitnessEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularSequenceClusterWitnessEventAtDefault index rest

def regularSequenceClusterWitnessFromEventFlow
    (ef : EventFlow) : Option RegularSequenceClusterWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularSequenceClusterWitnessUp.mk
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 0 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 1 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 2 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 3 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 4 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 5 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 6 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 7 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 8 ef))
      (regularSequenceClusterWitnessDecodeBHist
        (regularSequenceClusterWitnessEventAtDefault 9 ef)))

private theorem RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_round_trip
    (x : RegularSequenceClusterWitnessUp) :
    regularSequenceClusterWitnessFromEventFlow
      (regularSequenceClusterWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S F E D R Q H C P N =>
      change
        some
            (RegularSequenceClusterWitnessUp.mk
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist S))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist F))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist E))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist D))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist R))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist Q))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist H))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist C))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist P))
              (regularSequenceClusterWitnessDecodeBHist
                (regularSequenceClusterWitnessEncodeBHist N))) =
          some (RegularSequenceClusterWitnessUp.mk S F E D R Q H C P N)
      rw [RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode S,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode F,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode E,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode D,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode R,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode Q,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode H,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode C,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode P,
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularSequenceClusterWitnessUp} :
    regularSequenceClusterWitnessToEventFlow x =
      regularSequenceClusterWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularSequenceClusterWitnessFromEventFlow
          (regularSequenceClusterWitnessToEventFlow x) =
        regularSequenceClusterWitnessFromEventFlow
          (regularSequenceClusterWitnessToEventFlow y) :=
    congrArg regularSequenceClusterWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_round_trip y)))

instance regularSequenceClusterWitnessBHistCarrier :
    BHistCarrier RegularSequenceClusterWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularSequenceClusterWitnessToEventFlow
  fromEventFlow := regularSequenceClusterWitnessFromEventFlow

instance regularSequenceClusterWitnessChapterTasteGate :
    ChapterTasteGate RegularSequenceClusterWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularSequenceClusterWitnessFromEventFlow
        (regularSequenceClusterWitnessToEventFlow x) = some x
    exact RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularSequenceClusterWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularSequenceClusterWitnessDecodeBHist
      (regularSequenceClusterWitnessEncodeBHist h) = h) ∧
      (∀ x : RegularSequenceClusterWitnessUp,
        regularSequenceClusterWitnessFromEventFlow
          (regularSequenceClusterWitnessToEventFlow x) = some x) ∧
        (∀ x y : RegularSequenceClusterWitnessUp,
          regularSequenceClusterWitnessToEventFlow x =
            regularSequenceClusterWitnessToEventFlow y -> x = y) ∧
          regularSequenceClusterWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_decode_encode,
      RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularSequenceClusterWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularSequenceClusterWitnessUp
