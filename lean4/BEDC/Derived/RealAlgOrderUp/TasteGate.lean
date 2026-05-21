import BEDC.Derived.RealAlgOrderUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealAlgOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealAlgOrderUp : Type where
  | mk
      (endpoints readbacks dyadicOps schedule apartness orderLedger transports continuations
        provenance localNameCert : BHist) :
        RealAlgOrderUp
  deriving DecidableEq

def realAlgOrderTasteGateTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b0]

def realAlgOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realAlgOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realAlgOrderEncodeBHist h

def realAlgOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realAlgOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realAlgOrderDecodeBHist tail)

private theorem RealAlgOrderTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realAlgOrderDecodeBHist (realAlgOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realAlgOrderFields : RealAlgOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealAlgOrderUp.mk endpoints readbacks dyadicOps schedule apartness orderLedger transports
      continuations provenance localNameCert =>
      [endpoints, readbacks, dyadicOps, schedule, apartness, orderLedger, transports,
        continuations, provenance, localNameCert]

def realAlgOrderToEventFlow : RealAlgOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealAlgOrderUp.mk endpoints readbacks dyadicOps schedule apartness orderLedger transports
      continuations provenance localNameCert =>
      [realAlgOrderTasteGateTag,
        realAlgOrderEncodeBHist endpoints,
        realAlgOrderEncodeBHist readbacks,
        realAlgOrderEncodeBHist dyadicOps,
        realAlgOrderEncodeBHist schedule,
        realAlgOrderEncodeBHist apartness,
        realAlgOrderEncodeBHist orderLedger,
        realAlgOrderEncodeBHist transports,
        realAlgOrderEncodeBHist continuations,
        realAlgOrderEncodeBHist provenance,
        realAlgOrderEncodeBHist localNameCert]

private def RealAlgOrderTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealAlgOrderTasteGate_single_carrier_alignment_eventAt index rest

def realAlgOrderFromEventFlow : EventFlow → Option RealAlgOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealAlgOrderUp.mk
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 1 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 2 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 3 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 4 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 5 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 6 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 7 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 8 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 9 ef))
          (realAlgOrderDecodeBHist
            (RealAlgOrderTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem RealAlgOrderTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealAlgOrderUp, realAlgOrderFromEventFlow (realAlgOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk endpoints readbacks dyadicOps schedule apartness orderLedger transports continuations
      provenance localNameCert =>
      change
        some
          (RealAlgOrderUp.mk
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist endpoints))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist readbacks))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist dyadicOps))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist schedule))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist apartness))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist orderLedger))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist transports))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist continuations))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist provenance))
            (realAlgOrderDecodeBHist (realAlgOrderEncodeBHist localNameCert))) =
          some
            (RealAlgOrderUp.mk endpoints readbacks dyadicOps schedule apartness orderLedger
              transports continuations provenance localNameCert)
      rw [RealAlgOrderTasteGate_single_carrier_alignment_decode_encode endpoints,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode readbacks,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode dyadicOps,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode schedule,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode apartness,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode orderLedger,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode transports,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode continuations,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode provenance,
        RealAlgOrderTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem RealAlgOrderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealAlgOrderUp} :
    realAlgOrderToEventFlow x = realAlgOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realAlgOrderFromEventFlow (realAlgOrderToEventFlow x) =
        realAlgOrderFromEventFlow (realAlgOrderToEventFlow y) :=
    congrArg realAlgOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealAlgOrderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealAlgOrderTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealAlgOrderTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealAlgOrderUp, realAlgOrderFields x = realAlgOrderFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk endpoints₁ readbacks₁ dyadicOps₁ schedule₁ apartness₁ orderLedger₁ transports₁
      continuations₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk endpoints₂ readbacks₂ dyadicOps₂ schedule₂ apartness₂ orderLedger₂ transports₂
          continuations₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance realAlgOrderBHistCarrier : BHistCarrier RealAlgOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realAlgOrderToEventFlow
  fromEventFlow := realAlgOrderFromEventFlow

instance realAlgOrderChapterTasteGate : ChapterTasteGate RealAlgOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := RealAlgOrderTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealAlgOrderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realAlgOrderFieldFaithful : FieldFaithful RealAlgOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realAlgOrderFields
  field_faithful := RealAlgOrderTasteGate_single_carrier_alignment_fields_faithful

theorem RealAlgOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, realAlgOrderDecodeBHist (realAlgOrderEncodeBHist h) = h) ∧
      (∀ x : RealAlgOrderUp, realAlgOrderFromEventFlow (realAlgOrderToEventFlow x) = some x) ∧
        (∀ x y : RealAlgOrderUp, realAlgOrderToEventFlow x = realAlgOrderToEventFlow y →
          x = y) ∧
          realAlgOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealAlgOrderTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact RealAlgOrderTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y
        exact RealAlgOrderTasteGate_single_carrier_alignment_toEventFlow_injective
      · rfl

end BEDC.Derived.RealAlgOrderUp
