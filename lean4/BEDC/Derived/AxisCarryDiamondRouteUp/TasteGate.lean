import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AxisCarryDiamondRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AxisCarryDiamondRouteUp : Type where
  | mk
      (overlapSource carrySuccessorLeft carrySuccessorRight sharedNormalTarget routeLeft
        routeRight valueLedgerLeft valueLedgerRight targetNormality transport continuation
        provenance name : BHist) :
      AxisCarryDiamondRouteUp
  deriving DecidableEq

def axisCarryDiamondRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: axisCarryDiamondRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: axisCarryDiamondRouteEncodeBHist h

def axisCarryDiamondRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (axisCarryDiamondRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (axisCarryDiamondRouteDecodeBHist tail)

private theorem axisCarryDiamondRoute_decode_encode_bhist :
    ∀ h : BHist, axisCarryDiamondRouteDecodeBHist
      (axisCarryDiamondRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def axisCarryDiamondRouteToEventFlow : AxisCarryDiamondRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryDiamondRouteUp.mk overlapSource carrySuccessorLeft carrySuccessorRight
      sharedNormalTarget routeLeft routeRight valueLedgerLeft valueLedgerRight targetNormality
      transport continuation provenance name =>
      [[BMark.b0],
        axisCarryDiamondRouteEncodeBHist overlapSource,
        [BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist carrySuccessorLeft,
        [BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist carrySuccessorRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist sharedNormalTarget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist routeLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist routeRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist valueLedgerLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        axisCarryDiamondRouteEncodeBHist valueLedgerRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist targetNormality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        axisCarryDiamondRouteEncodeBHist name]

private def axisCarryDiamondRouteDecodePacket
    (overlapSource carrySuccessorLeft carrySuccessorRight sharedNormalTarget routeLeft
      routeRight valueLedgerLeft valueLedgerRight targetNormality transport continuation
      provenance name : RawEvent) : AxisCarryDiamondRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  AxisCarryDiamondRouteUp.mk
    (axisCarryDiamondRouteDecodeBHist overlapSource)
    (axisCarryDiamondRouteDecodeBHist carrySuccessorLeft)
    (axisCarryDiamondRouteDecodeBHist carrySuccessorRight)
    (axisCarryDiamondRouteDecodeBHist sharedNormalTarget)
    (axisCarryDiamondRouteDecodeBHist routeLeft)
    (axisCarryDiamondRouteDecodeBHist routeRight)
    (axisCarryDiamondRouteDecodeBHist valueLedgerLeft)
    (axisCarryDiamondRouteDecodeBHist valueLedgerRight)
    (axisCarryDiamondRouteDecodeBHist targetNormality)
    (axisCarryDiamondRouteDecodeBHist transport)
    (axisCarryDiamondRouteDecodeBHist continuation)
    (axisCarryDiamondRouteDecodeBHist provenance)
    (axisCarryDiamondRouteDecodeBHist name)

def axisCarryDiamondRouteFromEventFlow : EventFlow → Option AxisCarryDiamondRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: overlapSource :: _tag1 :: carrySuccessorLeft :: _tag2 ::
      carrySuccessorRight :: _tag3 :: sharedNormalTarget :: _tag4 :: routeLeft :: _tag5 ::
      routeRight :: _tag6 :: valueLedgerLeft :: _tag7 :: valueLedgerRight :: _tag8 ::
      targetNormality :: _tag9 :: transport :: _tag10 :: continuation :: _tag11 ::
      provenance :: _tag12 :: name :: [] =>
      some
        (axisCarryDiamondRouteDecodePacket overlapSource carrySuccessorLeft carrySuccessorRight
          sharedNormalTarget routeLeft routeRight valueLedgerLeft valueLedgerRight
          targetNormality transport continuation provenance name)
  | _ => none

private theorem axisCarryDiamondRoute_round_trip :
    ∀ x : AxisCarryDiamondRouteUp,
      axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk overlapSource carrySuccessorLeft carrySuccessorRight sharedNormalTarget routeLeft
      routeRight valueLedgerLeft valueLedgerRight targetNormality transport continuation
      provenance name =>
      change
        some
          (axisCarryDiamondRouteDecodePacket
            (axisCarryDiamondRouteEncodeBHist overlapSource)
            (axisCarryDiamondRouteEncodeBHist carrySuccessorLeft)
            (axisCarryDiamondRouteEncodeBHist carrySuccessorRight)
            (axisCarryDiamondRouteEncodeBHist sharedNormalTarget)
            (axisCarryDiamondRouteEncodeBHist routeLeft)
            (axisCarryDiamondRouteEncodeBHist routeRight)
            (axisCarryDiamondRouteEncodeBHist valueLedgerLeft)
            (axisCarryDiamondRouteEncodeBHist valueLedgerRight)
            (axisCarryDiamondRouteEncodeBHist targetNormality)
            (axisCarryDiamondRouteEncodeBHist transport)
            (axisCarryDiamondRouteEncodeBHist continuation)
            (axisCarryDiamondRouteEncodeBHist provenance)
            (axisCarryDiamondRouteEncodeBHist name)) =
          some
            (AxisCarryDiamondRouteUp.mk overlapSource carrySuccessorLeft carrySuccessorRight
              sharedNormalTarget routeLeft routeRight valueLedgerLeft valueLedgerRight
              targetNormality transport continuation provenance name)
      unfold axisCarryDiamondRouteDecodePacket
      rw [axisCarryDiamondRoute_decode_encode_bhist overlapSource,
        axisCarryDiamondRoute_decode_encode_bhist carrySuccessorLeft,
        axisCarryDiamondRoute_decode_encode_bhist carrySuccessorRight,
        axisCarryDiamondRoute_decode_encode_bhist sharedNormalTarget,
        axisCarryDiamondRoute_decode_encode_bhist routeLeft,
        axisCarryDiamondRoute_decode_encode_bhist routeRight,
        axisCarryDiamondRoute_decode_encode_bhist valueLedgerLeft,
        axisCarryDiamondRoute_decode_encode_bhist valueLedgerRight,
        axisCarryDiamondRoute_decode_encode_bhist targetNormality,
        axisCarryDiamondRoute_decode_encode_bhist transport,
        axisCarryDiamondRoute_decode_encode_bhist continuation,
        axisCarryDiamondRoute_decode_encode_bhist provenance,
        axisCarryDiamondRoute_decode_encode_bhist name]

private theorem axisCarryDiamondRouteToEventFlow_injective
    {x y : AxisCarryDiamondRouteUp} :
    axisCarryDiamondRouteToEventFlow x = axisCarryDiamondRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow x) =
        axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow y) :=
    congrArg axisCarryDiamondRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (axisCarryDiamondRoute_round_trip x).symm
      (Eq.trans hread (axisCarryDiamondRoute_round_trip y)))

private def axisCarryDiamondRouteFields : AxisCarryDiamondRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AxisCarryDiamondRouteUp.mk overlapSource carrySuccessorLeft carrySuccessorRight
      sharedNormalTarget routeLeft routeRight valueLedgerLeft valueLedgerRight targetNormality
      transport continuation provenance name =>
      [overlapSource, carrySuccessorLeft, carrySuccessorRight, sharedNormalTarget, routeLeft,
        routeRight, valueLedgerLeft, valueLedgerRight, targetNormality, transport, continuation,
        provenance, name]

private theorem axisCarryDiamondRoute_field_faithful :
    ∀ x y : AxisCarryDiamondRouteUp,
      axisCarryDiamondRouteFields x = axisCarryDiamondRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk overlapSource carrySuccessorLeft carrySuccessorRight sharedNormalTarget routeLeft
      routeRight valueLedgerLeft valueLedgerRight targetNormality transport continuation
      provenance name =>
      cases y with
      | mk overlapSource' carrySuccessorLeft' carrySuccessorRight' sharedNormalTarget'
          routeLeft' routeRight' valueLedgerLeft' valueLedgerRight' targetNormality'
          transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance axisCarryDiamondRouteBHistCarrier : BHistCarrier AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := axisCarryDiamondRouteToEventFlow
  fromEventFlow := axisCarryDiamondRouteFromEventFlow

instance axisCarryDiamondRouteChapterTasteGate :
    ChapterTasteGate AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change axisCarryDiamondRouteFromEventFlow (axisCarryDiamondRouteToEventFlow x) = some x
    exact axisCarryDiamondRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (axisCarryDiamondRouteToEventFlow_injective heq)

instance axisCarryDiamondRouteFieldFaithful :
    FieldFaithful AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := axisCarryDiamondRouteFields
  field_faithful := axisCarryDiamondRoute_field_faithful

instance axisCarryDiamondRouteNontrivial :
    Nontrivial AxisCarryDiamondRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AxisCarryDiamondRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AxisCarryDiamondRouteUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AxisCarryDiamondRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  axisCarryDiamondRouteChapterTasteGate

end BEDC.Derived.AxisCarryDiamondRouteUp
