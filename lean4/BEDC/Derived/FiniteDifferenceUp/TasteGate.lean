import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteDifferenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteDifferenceUp : Type where
  | mk (S H L D Q R E B T C P N : BHist) : FiniteDifferenceUp
  deriving DecidableEq

def finiteDifferenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDifferenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDifferenceEncodeBHist h

def finiteDifferenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDifferenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDifferenceDecodeBHist tail)

private theorem FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDifferenceFields : FiniteDifferenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDifferenceUp.mk S H L D Q R E B T C P N => [S, H, L, D, Q, R, E, B, T, C, P, N]

def finiteDifferenceToEventFlow : FiniteDifferenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (finiteDifferenceFields x).map finiteDifferenceEncodeBHist

private def FiniteDifferenceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      FiniteDifferenceTasteGate_single_carrier_alignment_eventAt index rest

def finiteDifferenceFromEventFlow (ef : EventFlow) : Option FiniteDifferenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteDifferenceUp.mk
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 8 ef))
      (finiteDifferenceDecodeBHist (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 9 ef))
      (finiteDifferenceDecodeBHist
        (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 10 ef))
      (finiteDifferenceDecodeBHist
        (FiniteDifferenceTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem FiniteDifferenceTasteGate_single_carrier_alignment_round_trip
    (x : FiniteDifferenceUp) :
    finiteDifferenceFromEventFlow (finiteDifferenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S H L D Q R E B T C P N =>
      change
        some
          (FiniteDifferenceUp.mk
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist S))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist H))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist L))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist D))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist Q))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist R))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist E))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist B))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist T))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist C))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist P))
            (finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist N))) =
          some (FiniteDifferenceUp.mk S H L D Q R E B T C P N)
      rw [FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode S,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode H,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode L,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode D,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode Q,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode R,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode E,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode B,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode T,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode C,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode P,
        FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteDifferenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteDifferenceUp} :
    finiteDifferenceToEventFlow x = finiteDifferenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDifferenceFromEventFlow (finiteDifferenceToEventFlow x) =
        finiteDifferenceFromEventFlow (finiteDifferenceToEventFlow y) :=
    congrArg finiteDifferenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteDifferenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteDifferenceTasteGate_single_carrier_alignment_round_trip y)))

instance finiteDifferenceBHistCarrier : BHistCarrier FiniteDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDifferenceToEventFlow
  fromEventFlow := finiteDifferenceFromEventFlow

instance finiteDifferenceChapterTasteGate : ChapterTasteGate FiniteDifferenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteDifferenceFromEventFlow (finiteDifferenceToEventFlow x) = some x
    exact FiniteDifferenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteDifferenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FiniteDifferenceTasteGate_single_carrier_alignment :
    (forall h : BHist, finiteDifferenceDecodeBHist (finiteDifferenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteDifferenceUp) ∧
        Nonempty (ChapterTasteGate FiniteDifferenceUp) ∧
          finiteDifferenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteDifferenceTasteGate_single_carrier_alignment_decode_encode,
      ⟨finiteDifferenceBHistCarrier⟩,
      ⟨finiteDifferenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteDifferenceUp
