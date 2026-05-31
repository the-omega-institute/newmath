import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularSequenceLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularSequenceLimitUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (S R Q E H C P N : BHist) : RegularSequenceLimitUp
  deriving DecidableEq

def regularSequenceLimitEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularSequenceLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularSequenceLimitEncodeBHist h

def regularSequenceLimitDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularSequenceLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularSequenceLimitDecodeBHist tail)

private theorem RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularSequenceLimitFields : RegularSequenceLimitUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularSequenceLimitUp.mk S R Q E H C P N => [S, R, Q, E, H, C, P, N]

def regularSequenceLimitToEventFlow : RegularSequenceLimitUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularSequenceLimitFields x).map regularSequenceLimitEncodeBHist

private def RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt index rest

def regularSequenceLimitFromEventFlow : EventFlow -> Option RegularSequenceLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularSequenceLimitUp.mk
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 0 ef))
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 1 ef))
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 2 ef))
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 3 ef))
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 4 ef))
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 5 ef))
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 6 ef))
        (regularSequenceLimitDecodeBHist
          (RegularSequenceLimitTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem RegularSequenceLimitTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularSequenceLimitUp,
      regularSequenceLimitFromEventFlow (regularSequenceLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R Q E H C P N =>
      change
        some
          (RegularSequenceLimitUp.mk
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist S))
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist R))
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist Q))
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist E))
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist H))
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist C))
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist P))
            (regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist N))) =
          some (RegularSequenceLimitUp.mk S R Q E H C P N)
      rw [RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode S,
        RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode R,
        RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode Q,
        RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode E,
        RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode H,
        RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode C,
        RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode P,
        RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularSequenceLimitUp} :
    regularSequenceLimitToEventFlow x = regularSequenceLimitToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularSequenceLimitFromEventFlow (regularSequenceLimitToEventFlow x) =
        regularSequenceLimitFromEventFlow (regularSequenceLimitToEventFlow y) :=
    congrArg regularSequenceLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularSequenceLimitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularSequenceLimitTasteGate_single_carrier_alignment_round_trip y)))

instance regularSequenceLimitBHistCarrier : BHistCarrier RegularSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularSequenceLimitToEventFlow
  fromEventFlow := regularSequenceLimitFromEventFlow

instance regularSequenceLimitChapterTasteGate : ChapterTasteGate RegularSequenceLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularSequenceLimitFromEventFlow (regularSequenceLimitToEventFlow x) = some x
    exact RegularSequenceLimitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularSequenceLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularSequenceLimitChapterTasteGate

theorem RegularSequenceLimitTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularSequenceLimitDecodeBHist (regularSequenceLimitEncodeBHist h) = h) ∧
      (forall x : RegularSequenceLimitUp,
        regularSequenceLimitFromEventFlow (regularSequenceLimitToEventFlow x) = some x) ∧
        (forall x y : RegularSequenceLimitUp,
          regularSequenceLimitToEventFlow x = regularSequenceLimitToEventFlow y -> x = y) ∧
          regularSequenceLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularSequenceLimitTasteGate_single_carrier_alignment_decode_encode,
      RegularSequenceLimitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularSequenceLimitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularSequenceLimitUp
