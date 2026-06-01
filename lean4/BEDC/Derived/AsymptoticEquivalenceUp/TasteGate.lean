import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AsymptoticEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AsymptoticEquivalenceUp : Type where
  | mk (S0 S1 R0 R1 D T E H C P N : BHist) : AsymptoticEquivalenceUp
  deriving DecidableEq

def asymptoticEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: asymptoticEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: asymptoticEquivalenceEncodeBHist h

def asymptoticEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (asymptoticEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (asymptoticEquivalenceDecodeBHist tail)

private theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def asymptoticEquivalenceFields :
    AsymptoticEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AsymptoticEquivalenceUp.mk S0 S1 R0 R1 D T E H C P N =>
      [S0, S1, R0, R1, D, T, E, H, C, P, N]

def asymptoticEquivalenceToEventFlow :
    AsymptoticEquivalenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (asymptoticEquivalenceFields x).map asymptoticEquivalenceEncodeBHist

private def AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault index rest

def asymptoticEquivalenceFromEventFlow
    (ef : EventFlow) : Option AsymptoticEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AsymptoticEquivalenceUp.mk
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (asymptoticEquivalenceDecodeBHist
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_eventAtDefault 10 ef)))

private theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip
    (x : AsymptoticEquivalenceUp) :
    asymptoticEquivalenceFromEventFlow
      (asymptoticEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S0 S1 R0 R1 D T E H C P N =>
      change
        some
          (AsymptoticEquivalenceUp.mk
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist S0))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist S1))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist R0))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist R1))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist D))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist T))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist E))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist H))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist C))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist P))
            (asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist N))) =
          some (AsymptoticEquivalenceUp.mk S0 S1 R0 R1 D T E H C P N)
      rw [AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode S0,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode S1,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode R0,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode R1,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode D,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode T,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode E,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode H,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode C,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode P,
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AsymptoticEquivalenceUp} :
    asymptoticEquivalenceToEventFlow x = asymptoticEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) =
        asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow y) :=
    congrArg asymptoticEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip y)))

instance asymptoticEquivalenceBHistCarrier :
    BHistCarrier AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := asymptoticEquivalenceToEventFlow
  fromEventFlow := asymptoticEquivalenceFromEventFlow

instance asymptoticEquivalenceChapterTasteGate :
    ChapterTasteGate AsymptoticEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      asymptoticEquivalenceFromEventFlow
        (asymptoticEquivalenceToEventFlow x) = some x
    exact AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (AsymptoticEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AsymptoticEquivalenceTasteGate_single_carrier_alignment :
    (∀ h : BHist, asymptoticEquivalenceDecodeBHist (asymptoticEquivalenceEncodeBHist h) = h) ∧
      (∀ x : AsymptoticEquivalenceUp,
        asymptoticEquivalenceFromEventFlow (asymptoticEquivalenceToEventFlow x) = some x) ∧
        (∀ x y : AsymptoticEquivalenceUp,
          asymptoticEquivalenceToEventFlow x = asymptoticEquivalenceToEventFlow y → x = y) ∧
          asymptoticEquivalenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨AsymptoticEquivalenceTasteGate_single_carrier_alignment_decode_encode,
      AsymptoticEquivalenceTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        AsymptoticEquivalenceTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.AsymptoticEquivalenceUp
