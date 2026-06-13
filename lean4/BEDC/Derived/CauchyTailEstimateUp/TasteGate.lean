import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailEstimateUp : Type where
  | mk (tail radius readback sealRow ledger : BHist) : CauchyTailEstimateUp
  deriving DecidableEq

def cauchyTailEstimateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailEstimateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailEstimateEncodeBHist h

def cauchyTailEstimateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailEstimateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailEstimateDecodeBHist tail)

private theorem CauchyTailEstimateUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyTailEstimateDecodeBHist (cauchyTailEstimateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailEstimateFields : CauchyTailEstimateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEstimateUp.mk tail radius readback sealRow ledger =>
      [tail, radius, readback, sealRow, ledger]

def cauchyTailEstimateToEventFlow : CauchyTailEstimateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailEstimateFields x).map cauchyTailEstimateEncodeBHist

private def cauchyTailEstimateEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyTailEstimateEventAt index rest

def cauchyTailEstimateFromEventFlow (ef : EventFlow) : Option CauchyTailEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTailEstimateUp.mk
      (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEventAt 0 ef))
      (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEventAt 1 ef))
      (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEventAt 2 ef))
      (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEventAt 3 ef))
      (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEventAt 4 ef)))

private theorem CauchyTailEstimateUpTasteGate_single_carrier_alignment_round_trip
    (x : CauchyTailEstimateUp) :
    cauchyTailEstimateFromEventFlow (cauchyTailEstimateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk tail radius readback sealRow ledger =>
      change
        some
          (CauchyTailEstimateUp.mk
            (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEncodeBHist tail))
            (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEncodeBHist radius))
            (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEncodeBHist readback))
            (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEncodeBHist sealRow))
            (cauchyTailEstimateDecodeBHist (cauchyTailEstimateEncodeBHist ledger))) =
          some (CauchyTailEstimateUp.mk tail radius readback sealRow ledger)
      rw [CauchyTailEstimateUpTasteGate_single_carrier_alignment_decode_encode tail,
        CauchyTailEstimateUpTasteGate_single_carrier_alignment_decode_encode radius,
        CauchyTailEstimateUpTasteGate_single_carrier_alignment_decode_encode readback,
        CauchyTailEstimateUpTasteGate_single_carrier_alignment_decode_encode sealRow,
        CauchyTailEstimateUpTasteGate_single_carrier_alignment_decode_encode ledger]

private theorem cauchyTailEstimateToEventFlow_injective {x y : CauchyTailEstimateUp} :
    cauchyTailEstimateToEventFlow x = cauchyTailEstimateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailEstimateFromEventFlow (cauchyTailEstimateToEventFlow x) =
        cauchyTailEstimateFromEventFlow (cauchyTailEstimateToEventFlow y) :=
    congrArg cauchyTailEstimateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailEstimateUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailEstimateUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyTailEstimateUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyTailEstimateUp,
      cauchyTailEstimateFields x = cauchyTailEstimateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk tail1 radius1 readback1 seal1 ledger1 =>
      cases y with
      | mk tail2 radius2 readback2 seal2 ledger2 =>
          cases hfields
          rfl

instance cauchyTailEstimateBHistCarrier : BHistCarrier CauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailEstimateToEventFlow
  fromEventFlow := cauchyTailEstimateFromEventFlow

instance cauchyTailEstimateChapterTasteGate : ChapterTasteGate CauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailEstimateFromEventFlow (cauchyTailEstimateToEventFlow x) = some x
    exact CauchyTailEstimateUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailEstimateToEventFlow_injective heq)

instance cauchyTailEstimateFieldFaithful : FieldFaithful CauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyTailEstimateFields
  field_faithful := CauchyTailEstimateUpTasteGate_single_carrier_alignment_fields_faithful

instance cauchyTailEstimateNontrivial : Nontrivial CauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailEstimateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailEstimateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyTailEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyTailEstimateChapterTasteGate

theorem CauchyTailEstimateUpTasteGate_single_carrier_alignment :
    (∀ x : CauchyTailEstimateUp,
      cauchyTailEstimateFromEventFlow (cauchyTailEstimateToEventFlow x) = some x) ∧
      (∀ x y : CauchyTailEstimateUp,
        cauchyTailEstimateToEventFlow x = cauchyTailEstimateToEventFlow y → x = y) ∧
      cauchyTailEstimateFields
          (CauchyTailEstimateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨CauchyTailEstimateUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => cauchyTailEstimateToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyTailEstimateUp
