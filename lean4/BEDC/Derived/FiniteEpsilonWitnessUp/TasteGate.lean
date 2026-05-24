import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteEpsilonWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteEpsilonWitnessUp : Type where
  | mk (E D W M R S H C P N : BHist) : FiniteEpsilonWitnessUp
  deriving DecidableEq

def finiteEpsilonWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteEpsilonWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteEpsilonWitnessEncodeBHist h

def finiteEpsilonWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteEpsilonWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteEpsilonWitnessDecodeBHist tail)

private theorem FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteEpsilonWitnessToEventFlow : FiniteEpsilonWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteEpsilonWitnessUp.mk E D W M R S H C P N =>
      [finiteEpsilonWitnessEncodeBHist E,
        finiteEpsilonWitnessEncodeBHist D,
        finiteEpsilonWitnessEncodeBHist W,
        finiteEpsilonWitnessEncodeBHist M,
        finiteEpsilonWitnessEncodeBHist R,
        finiteEpsilonWitnessEncodeBHist S,
        finiteEpsilonWitnessEncodeBHist H,
        finiteEpsilonWitnessEncodeBHist C,
        finiteEpsilonWitnessEncodeBHist P,
        finiteEpsilonWitnessEncodeBHist N]

private def FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault index rest

def finiteEpsilonWitnessFromEventFlow
    (ef : EventFlow) : Option FiniteEpsilonWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteEpsilonWitnessUp.mk
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (finiteEpsilonWitnessDecodeBHist
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

private theorem FiniteEpsilonWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteEpsilonWitnessUp,
      finiteEpsilonWitnessFromEventFlow (finiteEpsilonWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E D W M R S H C P N =>
      change
        some
          (FiniteEpsilonWitnessUp.mk
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist E))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist D))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist W))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist M))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist R))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist S))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist H))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist C))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist P))
            (finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist N))) =
          some (FiniteEpsilonWitnessUp.mk E D W M R S H C P N)
      rw [FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode E,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode D,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode W,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode M,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode R,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode S,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode H,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode C,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode P,
        FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode N]

private theorem FiniteEpsilonWitnessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteEpsilonWitnessUp} :
    finiteEpsilonWitnessToEventFlow x = finiteEpsilonWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteEpsilonWitnessFromEventFlow (finiteEpsilonWitnessToEventFlow x) =
        finiteEpsilonWitnessFromEventFlow (finiteEpsilonWitnessToEventFlow y) :=
    congrArg finiteEpsilonWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_round_trip y)))

instance finiteEpsilonWitnessBHistCarrier : BHistCarrier FiniteEpsilonWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteEpsilonWitnessToEventFlow
  fromEventFlow := finiteEpsilonWitnessFromEventFlow

instance finiteEpsilonWitnessChapterTasteGate :
    ChapterTasteGate FiniteEpsilonWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteEpsilonWitnessFromEventFlow (finiteEpsilonWitnessToEventFlow x) = some x
    exact FiniteEpsilonWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteEpsilonWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteEpsilonWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteEpsilonWitnessDecodeBHist (finiteEpsilonWitnessEncodeBHist h) = h) ∧
      (∀ x : FiniteEpsilonWitnessUp,
        finiteEpsilonWitnessFromEventFlow (finiteEpsilonWitnessToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteEpsilonWitnessUp,
          finiteEpsilonWitnessToEventFlow x = finiteEpsilonWitnessToEventFlow y →
            x = y) ∧
          finiteEpsilonWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact FiniteEpsilonWitnessTasteGate_single_carrier_alignment_decode
  constructor
  · exact FiniteEpsilonWitnessTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact FiniteEpsilonWitnessTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.FiniteEpsilonWitnessUp
