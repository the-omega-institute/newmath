import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BHistHendecaEventFlowNameCertUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BHistHendecaEventFlowNameCertUp : Type where
  | mk
      (tag source target encode0 encode1 encode2 encode3 encode4 encode5 encode6 encode7
        replay provenance localName : BHist) :
      BHistHendecaEventFlowNameCertUp
  deriving DecidableEq

def bHistHendecaEventFlowNameCertEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bHistHendecaEventFlowNameCertEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bHistHendecaEventFlowNameCertEncodeBHist h

def bHistHendecaEventFlowNameCertDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bHistHendecaEventFlowNameCertDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bHistHendecaEventFlowNameCertDecodeBHist tail)

theorem BHistHendecaEventFlowNameCertTasteGate_single_carrier_alignment_decode_aux :
    forall h : BHist,
      bHistHendecaEventFlowNameCertDecodeBHist
        (bHistHendecaEventFlowNameCertEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bHistHendecaEventFlowNameCertFields :
    BHistHendecaEventFlowNameCertUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHendecaEventFlowNameCertUp.mk tag source target encode0 encode1 encode2 encode3
      encode4 encode5 encode6 encode7 replay provenance localName =>
      [tag, source, target, encode0, encode1, encode2, encode3, encode4, encode5,
        encode6, encode7, replay, provenance, localName]

def bHistHendecaEventFlowNameCertToEventFlow :
    BHistHendecaEventFlowNameCertUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BHistHendecaEventFlowNameCertUp.mk tag source target encode0 encode1 encode2 encode3
      encode4 encode5 encode6 encode7 replay provenance localName =>
      [bHistHendecaEventFlowNameCertEncodeBHist tag,
        bHistHendecaEventFlowNameCertEncodeBHist source,
        bHistHendecaEventFlowNameCertEncodeBHist target,
        bHistHendecaEventFlowNameCertEncodeBHist encode0,
        bHistHendecaEventFlowNameCertEncodeBHist encode1,
        bHistHendecaEventFlowNameCertEncodeBHist encode2,
        bHistHendecaEventFlowNameCertEncodeBHist encode3,
        bHistHendecaEventFlowNameCertEncodeBHist encode4,
        bHistHendecaEventFlowNameCertEncodeBHist encode5,
        bHistHendecaEventFlowNameCertEncodeBHist encode6,
        bHistHendecaEventFlowNameCertEncodeBHist encode7,
        bHistHendecaEventFlowNameCertEncodeBHist replay,
        bHistHendecaEventFlowNameCertEncodeBHist provenance,
        bHistHendecaEventFlowNameCertEncodeBHist localName]

private def bHistHendecaEventFlowNameCertDecodePacket
    (tag source target encode0 encode1 encode2 encode3 encode4 encode5 encode6 encode7
      replay provenance localName : RawEvent) :
    BHistHendecaEventFlowNameCertUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BHistHendecaEventFlowNameCertUp.mk
    (bHistHendecaEventFlowNameCertDecodeBHist tag)
    (bHistHendecaEventFlowNameCertDecodeBHist source)
    (bHistHendecaEventFlowNameCertDecodeBHist target)
    (bHistHendecaEventFlowNameCertDecodeBHist encode0)
    (bHistHendecaEventFlowNameCertDecodeBHist encode1)
    (bHistHendecaEventFlowNameCertDecodeBHist encode2)
    (bHistHendecaEventFlowNameCertDecodeBHist encode3)
    (bHistHendecaEventFlowNameCertDecodeBHist encode4)
    (bHistHendecaEventFlowNameCertDecodeBHist encode5)
    (bHistHendecaEventFlowNameCertDecodeBHist encode6)
    (bHistHendecaEventFlowNameCertDecodeBHist encode7)
    (bHistHendecaEventFlowNameCertDecodeBHist replay)
    (bHistHendecaEventFlowNameCertDecodeBHist provenance)
    (bHistHendecaEventFlowNameCertDecodeBHist localName)

def bHistHendecaEventFlowNameCertFromEventFlow :
    EventFlow -> Option BHistHendecaEventFlowNameCertUp
  -- BEDC touchpoint anchor: BHist BMark
  | [tag, source, target, encode0, encode1, encode2, encode3, encode4, encode5,
      encode6, encode7, replay, provenance, localName] =>
      some
        (bHistHendecaEventFlowNameCertDecodePacket tag source target encode0 encode1
          encode2 encode3 encode4 encode5 encode6 encode7 replay provenance localName)
  | _ => none

instance bHistHendecaEventFlowNameCertBHistCarrier :
    BHistCarrier BHistHendecaEventFlowNameCertUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bHistHendecaEventFlowNameCertToEventFlow
  fromEventFlow := bHistHendecaEventFlowNameCertFromEventFlow

theorem BHistHendecaEventFlowNameCertTasteGate_single_carrier_alignment :
    (forall h : BHist,
      bHistHendecaEventFlowNameCertDecodeBHist
        (bHistHendecaEventFlowNameCertEncodeBHist h) = h) ∧
      bHistHendecaEventFlowNameCertEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark EventFlow
  constructor
  · exact BHistHendecaEventFlowNameCertTasteGate_single_carrier_alignment_decode_aux
  · rfl

end BEDC.Derived.BHistHendecaEventFlowNameCertUp
