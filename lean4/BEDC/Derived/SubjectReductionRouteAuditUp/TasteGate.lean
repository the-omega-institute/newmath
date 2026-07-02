import BEDC.Derived.SubjectReductionRouteAuditUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionRouteAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def subjectReductionRouteAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionRouteAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionRouteAuditEncodeBHist h

def subjectReductionRouteAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionRouteAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionRouteAuditDecodeBHist tail)

private theorem SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def subjectReductionRouteAuditToEventFlow : BEDC.Derived.SubjectReductionRouteAuditUp →
    EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.SubjectReductionRouteAuditUp.mk B E I U S H C P N =>
      [subjectReductionRouteAuditEncodeBHist B,
        subjectReductionRouteAuditEncodeBHist E,
        subjectReductionRouteAuditEncodeBHist I,
        subjectReductionRouteAuditEncodeBHist U,
        subjectReductionRouteAuditEncodeBHist S,
        subjectReductionRouteAuditEncodeBHist H,
        subjectReductionRouteAuditEncodeBHist C,
        subjectReductionRouteAuditEncodeBHist P,
        subjectReductionRouteAuditEncodeBHist N]

private def subjectReductionRouteAuditEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => subjectReductionRouteAuditEventAtDefault index rest

def subjectReductionRouteAuditDecodeEventFlow
    (ef : EventFlow) : BEDC.Derived.SubjectReductionRouteAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.SubjectReductionRouteAuditUp.mk
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 0 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 1 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 2 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 3 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 4 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 5 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 6 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 7 ef))
    (subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEventAtDefault 8 ef))

def subjectReductionRouteAuditFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.SubjectReductionRouteAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some (subjectReductionRouteAuditDecodeEventFlow ef)

private theorem SubjectReductionRouteAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.SubjectReductionRouteAuditUp,
      subjectReductionRouteAuditFromEventFlow
          (subjectReductionRouteAuditToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B E I U S H C P N =>
      change
        some
          (BEDC.Derived.SubjectReductionRouteAuditUp.mk
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist B))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist E))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist I))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist U))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist S))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist H))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist C))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist P))
            (subjectReductionRouteAuditDecodeBHist
              (subjectReductionRouteAuditEncodeBHist N))) =
          some (BEDC.Derived.SubjectReductionRouteAuditUp.mk B E I U S H C P N)
      rw [SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode B,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode E,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode I,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode U,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode S,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode H,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode C,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode P,
        SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode N]

private theorem SubjectReductionRouteAuditTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BEDC.Derived.SubjectReductionRouteAuditUp} :
    subjectReductionRouteAuditToEventFlow x = subjectReductionRouteAuditToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionRouteAuditFromEventFlow (subjectReductionRouteAuditToEventFlow x) =
        subjectReductionRouteAuditFromEventFlow (subjectReductionRouteAuditToEventFlow y) :=
    congrArg subjectReductionRouteAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SubjectReductionRouteAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SubjectReductionRouteAuditTasteGate_single_carrier_alignment_round_trip y)))

instance SubjectReductionRouteAuditTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BEDC.Derived.SubjectReductionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionRouteAuditToEventFlow
  fromEventFlow := subjectReductionRouteAuditFromEventFlow

instance SubjectReductionRouteAuditTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BEDC.Derived.SubjectReductionRouteAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionRouteAuditFromEventFlow (subjectReductionRouteAuditToEventFlow x) =
        some x
    exact SubjectReductionRouteAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SubjectReductionRouteAuditTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem SubjectReductionRouteAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      subjectReductionRouteAuditDecodeBHist (subjectReductionRouteAuditEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BEDC.Derived.SubjectReductionRouteAuditUp) ∧
        Nonempty (ChapterTasteGate BEDC.Derived.SubjectReductionRouteAuditUp) ∧
          subjectReductionRouteAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨SubjectReductionRouteAuditTasteGate_single_carrier_alignment_decode_encode,
      ⟨SubjectReductionRouteAuditTasteGate_single_carrier_alignment_BHistCarrier⟩,
      ⟨SubjectReductionRouteAuditTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SubjectReductionRouteAuditUp
