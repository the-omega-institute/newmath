import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffReflectionUp : Type where
  | mk
      (metric separated zeroDistance uniformRoute completionHandoff transport replay provenance
        localName : BHist) :
        HausdorffReflectionUp
  deriving DecidableEq

def hausdorffReflectionTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0, BMark.b0]

def hausdorffReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffReflectionEncodeBHist h

def hausdorffReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffReflectionDecodeBHist tail)

private theorem HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffReflectionFields : HausdorffReflectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffReflectionUp.mk metric separated zeroDistance uniformRoute completionHandoff
      transport replay provenance localName =>
      [metric, separated, zeroDistance, uniformRoute, completionHandoff, transport, replay,
        provenance, localName]

def hausdorffReflectionToEventFlow : HausdorffReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      hausdorffReflectionTag ::
        (hausdorffReflectionFields x).map hausdorffReflectionEncodeBHist

def hausdorffReflectionFromEventFlow : EventFlow → Option HausdorffReflectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, metric, separated, zeroDistance, uniformRoute, completionHandoff, transport, replay,
      provenance, localName] =>
      match tag with
      | [BMark.b1, BMark.b1, BMark.b0, BMark.b0] =>
          some
            (HausdorffReflectionUp.mk
              (hausdorffReflectionDecodeBHist metric)
              (hausdorffReflectionDecodeBHist separated)
              (hausdorffReflectionDecodeBHist zeroDistance)
              (hausdorffReflectionDecodeBHist uniformRoute)
              (hausdorffReflectionDecodeBHist completionHandoff)
              (hausdorffReflectionDecodeBHist transport)
              (hausdorffReflectionDecodeBHist replay)
              (hausdorffReflectionDecodeBHist provenance)
              (hausdorffReflectionDecodeBHist localName))
      | _ => none
  | _ => none

private theorem HausdorffReflectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffReflectionUp,
      hausdorffReflectionFromEventFlow (hausdorffReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric separated zeroDistance uniformRoute completionHandoff transport replay provenance
      localName =>
      change
        some
          (HausdorffReflectionUp.mk
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist metric))
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist separated))
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist zeroDistance))
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist uniformRoute))
            (hausdorffReflectionDecodeBHist
              (hausdorffReflectionEncodeBHist completionHandoff))
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist transport))
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist replay))
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist provenance))
            (hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist localName))) =
          some
            (HausdorffReflectionUp.mk metric separated zeroDistance uniformRoute
              completionHandoff transport replay provenance localName)
      rw [HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode metric,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode separated,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode zeroDistance,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode uniformRoute,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode completionHandoff,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode transport,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode replay,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode provenance,
        HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode localName]

private theorem HausdorffReflectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HausdorffReflectionUp} :
    hausdorffReflectionToEventFlow x = hausdorffReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffReflectionFromEventFlow (hausdorffReflectionToEventFlow x) =
        hausdorffReflectionFromEventFlow (hausdorffReflectionToEventFlow y) :=
    congrArg hausdorffReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HausdorffReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HausdorffReflectionTasteGate_single_carrier_alignment_round_trip y)))

private def hausdorffReflectionBHistCarrierDef : BHistCarrier HausdorffReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffReflectionToEventFlow
  fromEventFlow := hausdorffReflectionFromEventFlow

instance hausdorffReflectionBHistCarrier : BHistCarrier HausdorffReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffReflectionBHistCarrierDef

private def hausdorffReflectionChapterTasteGateDef :
    ChapterTasteGate HausdorffReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffReflectionFromEventFlow (hausdorffReflectionToEventFlow x) = some x
    exact HausdorffReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hausdorffReflectionChapterTasteGate : ChapterTasteGate HausdorffReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffReflectionChapterTasteGateDef

def taste_gate : ChapterTasteGate HausdorffReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffReflectionChapterTasteGate

theorem HausdorffReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, hausdorffReflectionDecodeBHist (hausdorffReflectionEncodeBHist h) = h) ∧
      hausdorffReflectionToEventFlow
          (HausdorffReflectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [[BMark.b1, BMark.b1, BMark.b0, BMark.b0], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  constructor
  · exact HausdorffReflectionTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.HausdorffReflectionUp
