import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CircleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CircleUp : Type where
  | mk (boundary coordinate metric compactness handoff : BHist) : CircleUp
  deriving DecidableEq

def circleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: circleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: circleEncodeBHist h

def circleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (circleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (circleDecodeBHist tail)

private theorem CircleUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, circleDecodeBHist (circleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def circleFields : CircleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CircleUp.mk boundary coordinate metric compactness handoff =>
      [boundary, coordinate, metric, compactness, handoff]

def circleToEventFlow : CircleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (circleFields x).map circleEncodeBHist

private def circleEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => circleEventAt index rest

def circleFromEventFlow (ef : EventFlow) : Option CircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CircleUp.mk
      (circleDecodeBHist (circleEventAt 0 ef))
      (circleDecodeBHist (circleEventAt 1 ef))
      (circleDecodeBHist (circleEventAt 2 ef))
      (circleDecodeBHist (circleEventAt 3 ef))
      (circleDecodeBHist (circleEventAt 4 ef)))

private theorem CircleUpTasteGate_single_carrier_alignment_round_trip
    (x : CircleUp) :
    circleFromEventFlow (circleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk boundary coordinate metric compactness handoff =>
      change
        some
          (CircleUp.mk
            (circleDecodeBHist (circleEncodeBHist boundary))
            (circleDecodeBHist (circleEncodeBHist coordinate))
            (circleDecodeBHist (circleEncodeBHist metric))
            (circleDecodeBHist (circleEncodeBHist compactness))
            (circleDecodeBHist (circleEncodeBHist handoff))) =
          some (CircleUp.mk boundary coordinate metric compactness handoff)
      rw [CircleUpTasteGate_single_carrier_alignment_decode_encode boundary,
        CircleUpTasteGate_single_carrier_alignment_decode_encode coordinate,
        CircleUpTasteGate_single_carrier_alignment_decode_encode metric,
        CircleUpTasteGate_single_carrier_alignment_decode_encode compactness,
        CircleUpTasteGate_single_carrier_alignment_decode_encode handoff]

private theorem circleToEventFlow_injective {x y : CircleUp} :
    circleToEventFlow x = circleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      circleFromEventFlow (circleToEventFlow x) =
        circleFromEventFlow (circleToEventFlow y) :=
    congrArg circleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CircleUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CircleUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem CircleUpTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CircleUp, circleFields x = circleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk boundary1 coordinate1 metric1 compactness1 handoff1 =>
      cases y with
      | mk boundary2 coordinate2 metric2 compactness2 handoff2 =>
          cases hfields
          rfl

instance circleBHistCarrier : BHistCarrier CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := circleToEventFlow
  fromEventFlow := circleFromEventFlow

instance circleChapterTasteGate : ChapterTasteGate CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change circleFromEventFlow (circleToEventFlow x) = some x
    exact CircleUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (circleToEventFlow_injective heq)

instance circleFieldFaithful : FieldFaithful CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := circleFields
  field_faithful := CircleUpTasteGate_single_carrier_alignment_fields_faithful

instance circleNontrivial : Nontrivial CircleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CircleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CircleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CircleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  circleChapterTasteGate

theorem CircleUpTasteGate_single_carrier_alignment :
    (∀ x : CircleUp, circleFromEventFlow (circleToEventFlow x) = some x) ∧
      (∀ x y : CircleUp, circleToEventFlow x = circleToEventFlow y → x = y) ∧
      circleFields (CircleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨CircleUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => circleToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CircleUp
