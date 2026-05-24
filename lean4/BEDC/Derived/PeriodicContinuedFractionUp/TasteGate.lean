import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PeriodicContinuedFractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PeriodicContinuedFractionUp : Type where
  | mk (I B L Q D S G E H C P N : BHist) : PeriodicContinuedFractionUp
  deriving DecidableEq

def periodicContinuedFractionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: periodicContinuedFractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: periodicContinuedFractionEncodeBHist h

def periodicContinuedFractionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (periodicContinuedFractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (periodicContinuedFractionDecodeBHist tail)

private theorem PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def periodicContinuedFractionToEventFlow : PeriodicContinuedFractionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PeriodicContinuedFractionUp.mk I B L Q D S G E H C P N =>
      [periodicContinuedFractionEncodeBHist I,
        periodicContinuedFractionEncodeBHist B,
        periodicContinuedFractionEncodeBHist L,
        periodicContinuedFractionEncodeBHist Q,
        periodicContinuedFractionEncodeBHist D,
        periodicContinuedFractionEncodeBHist S,
        periodicContinuedFractionEncodeBHist G,
        periodicContinuedFractionEncodeBHist E,
        periodicContinuedFractionEncodeBHist H,
        periodicContinuedFractionEncodeBHist C,
        periodicContinuedFractionEncodeBHist P,
        periodicContinuedFractionEncodeBHist N]

private def PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault index rest

def periodicContinuedFractionFromEventFlow
    (ef : EventFlow) : Option PeriodicContinuedFractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PeriodicContinuedFractionUp.mk
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (periodicContinuedFractionDecodeBHist
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_eventAtDefault 11 ef)))

private theorem PeriodicContinuedFractionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PeriodicContinuedFractionUp,
      periodicContinuedFractionFromEventFlow (periodicContinuedFractionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I B L Q D S G E H C P N =>
      change
        some
          (PeriodicContinuedFractionUp.mk
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist I))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist B))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist L))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist Q))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist D))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist S))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist G))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist E))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist H))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist C))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist P))
            (periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist N))) =
          some (PeriodicContinuedFractionUp.mk I B L Q D S G E H C P N)
      rw [PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode I,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode B,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode L,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode Q,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode D,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode S,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode G,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode E,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode H,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode C,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode P,
        PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode N]

private theorem PeriodicContinuedFractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PeriodicContinuedFractionUp} :
    periodicContinuedFractionToEventFlow x = periodicContinuedFractionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      periodicContinuedFractionFromEventFlow (periodicContinuedFractionToEventFlow x) =
        periodicContinuedFractionFromEventFlow (periodicContinuedFractionToEventFlow y) :=
    congrArg periodicContinuedFractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PeriodicContinuedFractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PeriodicContinuedFractionTasteGate_single_carrier_alignment_round_trip y)))

instance periodicContinuedFractionBHistCarrier :
    BHistCarrier PeriodicContinuedFractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := periodicContinuedFractionToEventFlow
  fromEventFlow := periodicContinuedFractionFromEventFlow

instance periodicContinuedFractionChapterTasteGate :
    ChapterTasteGate PeriodicContinuedFractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change periodicContinuedFractionFromEventFlow (periodicContinuedFractionToEventFlow x) =
      some x
    exact PeriodicContinuedFractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PeriodicContinuedFractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem PeriodicContinuedFractionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      periodicContinuedFractionDecodeBHist (periodicContinuedFractionEncodeBHist h) = h) ∧
      (∀ x : PeriodicContinuedFractionUp,
        periodicContinuedFractionFromEventFlow (periodicContinuedFractionToEventFlow x) =
          some x) ∧
        (∀ x y : PeriodicContinuedFractionUp,
          periodicContinuedFractionToEventFlow x = periodicContinuedFractionToEventFlow y →
            x = y) ∧
          periodicContinuedFractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact PeriodicContinuedFractionTasteGate_single_carrier_alignment_decode
  constructor
  · exact PeriodicContinuedFractionTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact PeriodicContinuedFractionTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.PeriodicContinuedFractionUp
