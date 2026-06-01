import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalCauchySubsequenceUp : Type where
  | mk : (S R T Q H C P N : BHist) -> DiagonalCauchySubsequenceUp

def diagonalCauchySubsequenceEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalCauchySubsequenceEncodeBHist h

def diagonalCauchySubsequenceDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalCauchySubsequenceDecodeBHist tail)

theorem DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      diagonalCauchySubsequenceDecodeBHist (diagonalCauchySubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def diagonalCauchySubsequenceFields : DiagonalCauchySubsequenceUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalCauchySubsequenceUp.mk S R T Q H C P N => [S, R, T, Q, H, C, P, N]

def diagonalCauchySubsequenceToEventFlow : DiagonalCauchySubsequenceUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (diagonalCauchySubsequenceFields x).map diagonalCauchySubsequenceEncodeBHist

def diagonalCauchySubsequenceEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => diagonalCauchySubsequenceEventAtDefault index rest

def diagonalCauchySubsequenceFromEventFlow :
    EventFlow -> Option DiagonalCauchySubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DiagonalCauchySubsequenceUp.mk
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 0 ef))
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 1 ef))
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 2 ef))
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 3 ef))
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 4 ef))
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 5 ef))
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 6 ef))
          (diagonalCauchySubsequenceDecodeBHist
            (diagonalCauchySubsequenceEventAtDefault 7 ef)))

theorem DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DiagonalCauchySubsequenceUp,
      diagonalCauchySubsequenceFromEventFlow
        (diagonalCauchySubsequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R T Q H C P N =>
      change
        some
          (DiagonalCauchySubsequenceUp.mk
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist S))
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist R))
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist T))
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist Q))
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist H))
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist C))
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist P))
            (diagonalCauchySubsequenceDecodeBHist
              (diagonalCauchySubsequenceEncodeBHist N))) =
          some (DiagonalCauchySubsequenceUp.mk S R T Q H C P N)
      rw [DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode S,
        DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode R,
        DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode T,
        DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode Q,
        DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode H,
        DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode C,
        DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode P,
        DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode N]

theorem DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_injective
    {x y : DiagonalCauchySubsequenceUp} :
    diagonalCauchySubsequenceToEventFlow x = diagonalCauchySubsequenceToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalCauchySubsequenceFromEventFlow (diagonalCauchySubsequenceToEventFlow x) =
        diagonalCauchySubsequenceFromEventFlow (diagonalCauchySubsequenceToEventFlow y) :=
    congrArg diagonalCauchySubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip y)))

instance diagonalCauchySubsequenceBHistCarrier :
    BHistCarrier DiagonalCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalCauchySubsequenceToEventFlow
  fromEventFlow := diagonalCauchySubsequenceFromEventFlow

instance diagonalCauchySubsequenceChapterTasteGate :
    ChapterTasteGate DiagonalCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate DiagonalCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalCauchySubsequenceChapterTasteGate

theorem DiagonalCauchySubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      diagonalCauchySubsequenceDecodeBHist (diagonalCauchySubsequenceEncodeBHist h) = h) ∧
      (∀ x : DiagonalCauchySubsequenceUp,
        diagonalCauchySubsequenceFromEventFlow
          (diagonalCauchySubsequenceToEventFlow x) = some x) ∧
        (∀ x y : DiagonalCauchySubsequenceUp,
          diagonalCauchySubsequenceToEventFlow x =
            diagonalCauchySubsequenceToEventFlow y -> x = y) ∧
          diagonalCauchySubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_decode
  · constructor
    · exact DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact DiagonalCauchySubsequenceTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.DiagonalCauchySubsequenceUp
