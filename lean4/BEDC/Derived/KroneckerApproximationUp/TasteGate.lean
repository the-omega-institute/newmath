import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KroneckerApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KroneckerApproximationUp : Type where
  | mk (S W M D T U G R E H C P N : BHist) : KroneckerApproximationUp
  deriving DecidableEq

def kroneckerApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kroneckerApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kroneckerApproximationEncodeBHist h

def kroneckerApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kroneckerApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kroneckerApproximationDecodeBHist tail)

private theorem KroneckerApproximationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kroneckerApproximationToEventFlow : KroneckerApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KroneckerApproximationUp.mk S W M D T U G R E H C P N =>
      [kroneckerApproximationEncodeBHist S,
        kroneckerApproximationEncodeBHist W,
        kroneckerApproximationEncodeBHist M,
        kroneckerApproximationEncodeBHist D,
        kroneckerApproximationEncodeBHist T,
        kroneckerApproximationEncodeBHist U,
        kroneckerApproximationEncodeBHist G,
        kroneckerApproximationEncodeBHist R,
        kroneckerApproximationEncodeBHist E,
        kroneckerApproximationEncodeBHist H,
        kroneckerApproximationEncodeBHist C,
        kroneckerApproximationEncodeBHist P,
        kroneckerApproximationEncodeBHist N]

private def KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault index rest

def kroneckerApproximationFromEventFlow
    (ef : EventFlow) : Option KroneckerApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KroneckerApproximationUp.mk
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 10 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (kroneckerApproximationDecodeBHist
        (KroneckerApproximationTasteGate_single_carrier_alignment_eventAtDefault 12 ef)))

private theorem KroneckerApproximationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : KroneckerApproximationUp,
      kroneckerApproximationFromEventFlow (kroneckerApproximationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W M D T U G R E H C P N =>
      change
        some
          (KroneckerApproximationUp.mk
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist S))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist W))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist M))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist D))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist T))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist U))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist G))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist R))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist E))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist H))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist C))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist P))
            (kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist N))) =
          some (KroneckerApproximationUp.mk S W M D T U G R E H C P N)
      rw [KroneckerApproximationTasteGate_single_carrier_alignment_decode S,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode W,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode M,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode D,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode T,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode U,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode G,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode R,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode E,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode H,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode C,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode P,
        KroneckerApproximationTasteGate_single_carrier_alignment_decode N]

private theorem KroneckerApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KroneckerApproximationUp} :
    kroneckerApproximationToEventFlow x = kroneckerApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kroneckerApproximationFromEventFlow (kroneckerApproximationToEventFlow x) =
        kroneckerApproximationFromEventFlow (kroneckerApproximationToEventFlow y) :=
    congrArg kroneckerApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KroneckerApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KroneckerApproximationTasteGate_single_carrier_alignment_round_trip y)))

instance kroneckerApproximationBHistCarrier :
    BHistCarrier KroneckerApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kroneckerApproximationToEventFlow
  fromEventFlow := kroneckerApproximationFromEventFlow

instance kroneckerApproximationChapterTasteGate :
    ChapterTasteGate KroneckerApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kroneckerApproximationFromEventFlow (kroneckerApproximationToEventFlow x) =
      some x
    exact KroneckerApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (KroneckerApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem KroneckerApproximationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kroneckerApproximationDecodeBHist (kroneckerApproximationEncodeBHist h) = h) ∧
      (∀ x : KroneckerApproximationUp,
        kroneckerApproximationFromEventFlow (kroneckerApproximationToEventFlow x) =
          some x) ∧
        (∀ x y : KroneckerApproximationUp,
          kroneckerApproximationToEventFlow x = kroneckerApproximationToEventFlow y →
            x = y) ∧
          kroneckerApproximationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact KroneckerApproximationTasteGate_single_carrier_alignment_decode
  constructor
  · exact KroneckerApproximationTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact KroneckerApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

end BEDC.Derived.KroneckerApproximationUp
