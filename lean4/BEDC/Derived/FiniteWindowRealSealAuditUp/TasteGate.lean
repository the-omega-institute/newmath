import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowRealSealAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowRealSealAuditUp : Type where
  | mk :
      (window tolerance readback sealRow refusal transport route provenance name : BHist) →
      FiniteWindowRealSealAuditUp
  deriving DecidableEq

def finiteWindowRealSealAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowRealSealAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowRealSealAuditEncodeBHist h

def finiteWindowRealSealAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowRealSealAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowRealSealAuditDecodeBHist tail)

private theorem finiteWindowRealSealAuditDecodeEncodeBHist :
    ∀ h : BHist,
      finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteWindowRealSealAuditFields :
    FiniteWindowRealSealAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowRealSealAuditUp.mk window tolerance readback sealRow refusal transport route
      provenance name =>
      [window, tolerance, readback, sealRow, refusal, transport, route, provenance, name]

def finiteWindowRealSealAuditToEventFlow :
    FiniteWindowRealSealAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteWindowRealSealAuditFields x).map finiteWindowRealSealAuditEncodeBHist

def finiteWindowRealSealAuditFromEventFlow :
    EventFlow → Option FiniteWindowRealSealAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [window, tolerance, readback, sealRow, refusal, transport, route, provenance, name] =>
      some
        (FiniteWindowRealSealAuditUp.mk
          (finiteWindowRealSealAuditDecodeBHist window)
          (finiteWindowRealSealAuditDecodeBHist tolerance)
          (finiteWindowRealSealAuditDecodeBHist readback)
          (finiteWindowRealSealAuditDecodeBHist sealRow)
          (finiteWindowRealSealAuditDecodeBHist refusal)
          (finiteWindowRealSealAuditDecodeBHist transport)
          (finiteWindowRealSealAuditDecodeBHist route)
          (finiteWindowRealSealAuditDecodeBHist provenance)
          (finiteWindowRealSealAuditDecodeBHist name))
  | _ => none

private theorem finiteWindowRealSealAudit_round_trip :
    ∀ x : FiniteWindowRealSealAuditUp,
      finiteWindowRealSealAuditFromEventFlow
        (finiteWindowRealSealAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window tolerance readback sealRow refusal transport route provenance name =>
      change
        some
          (FiniteWindowRealSealAuditUp.mk
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist window))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist tolerance))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist readback))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist sealRow))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist refusal))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist transport))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist route))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist provenance))
            (finiteWindowRealSealAuditDecodeBHist
              (finiteWindowRealSealAuditEncodeBHist name))) =
          some
            (FiniteWindowRealSealAuditUp.mk window tolerance readback sealRow refusal transport
              route provenance name)
      rw [finiteWindowRealSealAuditDecodeEncodeBHist window,
        finiteWindowRealSealAuditDecodeEncodeBHist tolerance,
        finiteWindowRealSealAuditDecodeEncodeBHist readback,
        finiteWindowRealSealAuditDecodeEncodeBHist sealRow,
        finiteWindowRealSealAuditDecodeEncodeBHist refusal,
        finiteWindowRealSealAuditDecodeEncodeBHist transport,
        finiteWindowRealSealAuditDecodeEncodeBHist route,
        finiteWindowRealSealAuditDecodeEncodeBHist provenance,
        finiteWindowRealSealAuditDecodeEncodeBHist name]

private theorem finiteWindowRealSealAuditToEventFlow_injective
    {x y : FiniteWindowRealSealAuditUp} :
    finiteWindowRealSealAuditToEventFlow x =
      finiteWindowRealSealAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowRealSealAuditFromEventFlow (finiteWindowRealSealAuditToEventFlow x) =
        finiteWindowRealSealAuditFromEventFlow (finiteWindowRealSealAuditToEventFlow y) :=
    congrArg finiteWindowRealSealAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteWindowRealSealAudit_round_trip x).symm
      (Eq.trans hread (finiteWindowRealSealAudit_round_trip y)))

private theorem finiteWindowRealSealAudit_field_faithful :
    ∀ x y : FiniteWindowRealSealAuditUp,
      finiteWindowRealSealAuditFields x = finiteWindowRealSealAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk window₁ tolerance₁ readback₁ sealRow₁ refusal₁ transport₁ route₁ provenance₁ name₁ =>
      cases y with
      | mk window₂ tolerance₂ readback₂ sealRow₂ refusal₂ transport₂ route₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance finiteWindowRealSealAuditBHistCarrier :
    BHistCarrier FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowRealSealAuditToEventFlow
  fromEventFlow := finiteWindowRealSealAuditFromEventFlow

instance finiteWindowRealSealAuditChapterTasteGate :
    ChapterTasteGate FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteWindowRealSealAuditFromEventFlow
        (finiteWindowRealSealAuditToEventFlow x) = some x
    exact finiteWindowRealSealAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowRealSealAuditToEventFlow_injective heq)

instance finiteWindowRealSealAuditFieldFaithful :
    FieldFaithful FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteWindowRealSealAuditFields
  field_faithful := finiteWindowRealSealAudit_field_faithful

instance finiteWindowRealSealAuditNontrivial :
    Nontrivial FiniteWindowRealSealAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWindowRealSealAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteWindowRealSealAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteWindowRealSealAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowRealSealAuditChapterTasteGate

theorem FiniteWindowRealSealAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteWindowRealSealAuditDecodeBHist
        (finiteWindowRealSealAuditEncodeBHist h) = h) ∧
      finiteWindowRealSealAuditEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : FiniteWindowRealSealAuditUp,
          finiteWindowRealSealAuditFields x = finiteWindowRealSealAuditFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact finiteWindowRealSealAuditDecodeEncodeBHist
  · constructor
    · rfl
    · exact finiteWindowRealSealAudit_field_faithful

end BEDC.Derived.FiniteWindowRealSealAuditUp
