import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountableDenseSubsetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountableDenseSubsetUp : Type where
  | packet
      (metric candidates window tolerance handoff distanceSeal transport replay provenance
        nameRow : BHist) : CountableDenseSubsetUp
  deriving DecidableEq, Repr

def countableDenseSubsetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countableDenseSubsetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countableDenseSubsetEncodeBHist h

def countableDenseSubsetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countableDenseSubsetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countableDenseSubsetDecodeBHist tail)

private theorem CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def countableDenseSubsetFields : CountableDenseSubsetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CountableDenseSubsetUp.packet metric candidates window tolerance handoff distanceSeal
      transport replay provenance nameRow =>
      [metric, candidates, window, tolerance, handoff, distanceSeal, transport, replay,
        provenance, nameRow]

def countableDenseSubsetToEventFlow : CountableDenseSubsetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (countableDenseSubsetFields x).map countableDenseSubsetEncodeBHist

private def countableDenseSubsetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => countableDenseSubsetEventAt index rest

def countableDenseSubsetFromEventFlow (ef : EventFlow) : Option CountableDenseSubsetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CountableDenseSubsetUp.packet
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 0 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 1 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 2 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 3 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 4 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 5 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 6 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 7 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 8 ef))
      (countableDenseSubsetDecodeBHist (countableDenseSubsetEventAt 9 ef)))

private theorem CountableDenseSubsetTasteGate_single_carrier_alignment_round_trip
    (x : CountableDenseSubsetUp) :
    countableDenseSubsetFromEventFlow (countableDenseSubsetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet metric candidates window tolerance handoff distanceSeal transport replay provenance
      nameRow =>
      change
        some
          (CountableDenseSubsetUp.packet
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist metric))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist candidates))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist window))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist tolerance))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist handoff))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist distanceSeal))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist transport))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist replay))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist provenance))
            (countableDenseSubsetDecodeBHist (countableDenseSubsetEncodeBHist nameRow))) =
          some
            (CountableDenseSubsetUp.packet metric candidates window tolerance handoff
              distanceSeal transport replay provenance nameRow)
      rw [CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode metric,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode candidates,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode window,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode tolerance,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode handoff,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode distanceSeal,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode transport,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode replay,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode provenance,
        CountableDenseSubsetTasteGate_single_carrier_alignment_decode_encode nameRow]

private theorem CountableDenseSubsetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CountableDenseSubsetUp} :
    countableDenseSubsetToEventFlow x = countableDenseSubsetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countableDenseSubsetFromEventFlow (countableDenseSubsetToEventFlow x) =
        countableDenseSubsetFromEventFlow (countableDenseSubsetToEventFlow y) :=
    congrArg countableDenseSubsetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CountableDenseSubsetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CountableDenseSubsetTasteGate_single_carrier_alignment_round_trip y)))

instance countableDenseSubsetBHistCarrier : BHistCarrier CountableDenseSubsetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countableDenseSubsetToEventFlow
  fromEventFlow := countableDenseSubsetFromEventFlow

instance countableDenseSubsetChapterTasteGate : ChapterTasteGate CountableDenseSubsetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change countableDenseSubsetFromEventFlow (countableDenseSubsetToEventFlow x) = some x
    exact CountableDenseSubsetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CountableDenseSubsetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CountableDenseSubsetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CountableDenseSubsetUp) ∧
      (∃ x : CountableDenseSubsetUp, List.Mem [BMark.b0] (BHistCarrier.toEventFlow x)) ∧
        (∀ x : CountableDenseSubsetUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨countableDenseSubsetChapterTasteGate⟩
  · constructor
    · exact
        ⟨CountableDenseSubsetUp.packet (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          List.Mem.head _⟩
    · intro x
      change countableDenseSubsetFromEventFlow (countableDenseSubsetToEventFlow x) = some x
      exact CountableDenseSubsetTasteGate_single_carrier_alignment_round_trip x

end BEDC.Derived.CountableDenseSubsetUp.TasteGate
