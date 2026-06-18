import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedConvergenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedConvergenceUp : Type where
  | mk (F U W R E I H C P N : BHist) : RegulatedConvergenceUp

def regulatedConvergenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedConvergenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedConvergenceEncodeBHist h

def regulatedConvergenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedConvergenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedConvergenceDecodeBHist tail)

private theorem RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedConvergenceFields : RegulatedConvergenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedConvergenceUp.mk F U W R E I H C P N => [F, U, W, R, E, I, H, C, P, N]

def regulatedConvergenceToEventFlow : RegulatedConvergenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regulatedConvergenceFields x).map regulatedConvergenceEncodeBHist

private def RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt index rest

def regulatedConvergenceFromEventFlow (ef : EventFlow) : Option RegulatedConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegulatedConvergenceUp.mk
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 0 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 1 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 2 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 3 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 4 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 5 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 6 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 7 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 8 ef))
      (regulatedConvergenceDecodeBHist
        (RegulatedConvergenceTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem RegulatedConvergenceTasteGate_single_carrier_alignment_round_trip
    (x : RegulatedConvergenceUp) :
    regulatedConvergenceFromEventFlow (regulatedConvergenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F U W R E I H C P N =>
      change
        some
          (RegulatedConvergenceUp.mk
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist F))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist U))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist W))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist R))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist E))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist I))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist H))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist C))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist P))
            (regulatedConvergenceDecodeBHist (regulatedConvergenceEncodeBHist N))) =
          some (RegulatedConvergenceUp.mk F U W R E I H C P N)
      rw [RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode F,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode U,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode W,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode R,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode E,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode I,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode H,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode C,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode P,
        RegulatedConvergenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegulatedConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedConvergenceUp} :
    regulatedConvergenceToEventFlow x = regulatedConvergenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedConvergenceFromEventFlow (regulatedConvergenceToEventFlow x) =
        regulatedConvergenceFromEventFlow (regulatedConvergenceToEventFlow y) :=
    congrArg regulatedConvergenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegulatedConvergenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegulatedConvergenceTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedConvergenceBHistCarrier : BHistCarrier RegulatedConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedConvergenceToEventFlow
  fromEventFlow := regulatedConvergenceFromEventFlow

instance regulatedConvergenceChapterTasteGate : ChapterTasteGate RegulatedConvergenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedConvergenceFromEventFlow (regulatedConvergenceToEventFlow x) = some x
    exact RegulatedConvergenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatedConvergenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def RegulatedConvergenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegulatedConvergenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedConvergenceChapterTasteGate

theorem RegulatedConvergenceTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegulatedConvergenceUp) ∧
      Nonempty (ChapterTasteGate RegulatedConvergenceUp) ∧
        ∃ x : RegulatedConvergenceUp,
          regulatedConvergenceFields x =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨regulatedConvergenceBHistCarrier⟩, ⟨regulatedConvergenceChapterTasteGate⟩,
      ⟨RegulatedConvergenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩⟩

end BEDC.Derived.RegulatedConvergenceUp
