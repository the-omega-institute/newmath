import BEDC.Derived.SeqUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeqUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeqUp : Type where
  | mk (indexWitness pointCarrierWitness modulusLedger : BHist) : SeqUp
  deriving DecidableEq

def seqTasteGateTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def seqEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: seqEncodeBHist h
  | BHist.e1 h => BMark.b1 :: seqEncodeBHist h

def seqDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (seqDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (seqDecodeBHist tail)

private theorem SeqTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, seqDecodeBHist (seqEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def seqFields : SeqUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeqUp.mk indexWitness pointCarrierWitness modulusLedger =>
      [indexWitness, pointCarrierWitness, modulusLedger]

def seqToEventFlow : SeqUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeqUp.mk indexWitness pointCarrierWitness modulusLedger =>
      [seqTasteGateTag,
        seqEncodeBHist indexWitness,
        seqEncodeBHist pointCarrierWitness,
        seqEncodeBHist modulusLedger]

private def SeqTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => SeqTasteGate_single_carrier_alignment_eventAt index rest

def seqFromEventFlow : EventFlow → Option SeqUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SeqUp.mk
          (seqDecodeBHist (SeqTasteGate_single_carrier_alignment_eventAt 1 ef))
          (seqDecodeBHist (SeqTasteGate_single_carrier_alignment_eventAt 2 ef))
          (seqDecodeBHist (SeqTasteGate_single_carrier_alignment_eventAt 3 ef)))

private theorem SeqTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SeqUp, seqFromEventFlow (seqToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk indexWitness pointCarrierWitness modulusLedger =>
      change
        some
          (SeqUp.mk
            (seqDecodeBHist (seqEncodeBHist indexWitness))
            (seqDecodeBHist (seqEncodeBHist pointCarrierWitness))
            (seqDecodeBHist (seqEncodeBHist modulusLedger))) =
          some (SeqUp.mk indexWitness pointCarrierWitness modulusLedger)
      rw [SeqTasteGate_single_carrier_alignment_decode_encode indexWitness,
        SeqTasteGate_single_carrier_alignment_decode_encode pointCarrierWitness,
        SeqTasteGate_single_carrier_alignment_decode_encode modulusLedger]

private theorem SeqTasteGate_single_carrier_alignment_toEventFlow_injective {x y : SeqUp} :
    seqToEventFlow x = seqToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread : seqFromEventFlow (seqToEventFlow x) = seqFromEventFlow (seqToEventFlow y) :=
    congrArg seqFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SeqTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SeqTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeqTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SeqUp, seqFields x = seqFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk indexWitness₁ pointCarrierWitness₁ modulusLedger₁ =>
      cases y with
      | mk indexWitness₂ pointCarrierWitness₂ modulusLedger₂ =>
          cases hfields
          rfl

instance seqBHistCarrier : BHistCarrier SeqUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := seqToEventFlow
  fromEventFlow := seqFromEventFlow

instance seqChapterTasteGate : ChapterTasteGate SeqUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := SeqTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeqTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance seqFieldFaithful : FieldFaithful SeqUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := seqFields
  field_faithful := SeqTasteGate_single_carrier_alignment_fields_faithful

theorem SeqTasteGate_single_carrier_alignment :
    (∀ h : BHist, seqDecodeBHist (seqEncodeBHist h) = h) ∧
      (∀ x : SeqUp, seqFromEventFlow (seqToEventFlow x) = some x) ∧
        (∀ x y : SeqUp, seqToEventFlow x = seqToEventFlow y → x = y) ∧
          seqEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SeqTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact SeqTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y
        exact SeqTasteGate_single_carrier_alignment_toEventFlow_injective
      · rfl

end BEDC.Derived.SeqUp
