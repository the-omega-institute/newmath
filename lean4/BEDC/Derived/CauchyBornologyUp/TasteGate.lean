import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyBornologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyBornologyUp : Type where
  | mk (boundedFamily radiusBudget ballLedger streamWindow rateSchedule regularReadback
      realSeal transport replay provenance localName : BHist) : CauchyBornologyUp
  deriving DecidableEq

def CauchyBornologyTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyBornologyTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyBornologyTasteGate_single_carrier_alignment_encodeBHist h

def CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyBornologyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist
          (CauchyBornologyTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyBornologyTasteGate_single_carrier_alignment_fields :
    CauchyBornologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyBornologyUp.mk boundedFamily radiusBudget ballLedger streamWindow rateSchedule
      regularReadback realSeal transport replay provenance localName =>
      [boundedFamily, radiusBudget, ballLedger, streamWindow, rateSchedule, regularReadback,
        realSeal, transport, replay, provenance, localName]

def CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow :
    CauchyBornologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyBornologyTasteGate_single_carrier_alignment_fields x).map
      CauchyBornologyTasteGate_single_carrier_alignment_encodeBHist

def CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyBornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | boundedFamily :: radiusBudget :: ballLedger :: streamWindow :: rateSchedule ::
      regularReadback :: realSeal :: transport :: replay :: provenance :: localName :: [] =>
      some
        (CauchyBornologyUp.mk
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist boundedFamily)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist radiusBudget)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist ballLedger)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist streamWindow)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist rateSchedule)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist regularReadback)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist realSeal)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist transport)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist replay)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist provenance)
          (CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist localName))
  | _ => none

private theorem CauchyBornologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyBornologyUp,
      CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk boundedFamily radiusBudget ballLedger streamWindow rateSchedule regularReadback
      realSeal transport replay provenance localName =>
      simp only [CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow,
        CauchyBornologyTasteGate_single_carrier_alignment_fields,
        CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, CauchyBornologyTasteGate_single_carrier_alignment_decode_encode]

private theorem CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyBornologyUp} :
    CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CauchyBornologyTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow
            (CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := CauchyBornologyTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem CauchyBornologyTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyBornologyUp,
      CauchyBornologyTasteGate_single_carrier_alignment_fields x =
          CauchyBornologyTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk boundedFamily₁ radiusBudget₁ ballLedger₁ streamWindow₁ rateSchedule₁
      regularReadback₁ realSeal₁ transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk boundedFamily₂ radiusBudget₂ ballLedger₂ streamWindow₂ rateSchedule₂
          regularReadback₂ realSeal₂ transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance CauchyBornologyTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyBornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyBornologyTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyBornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyBornologyTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyBornologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyBornologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CauchyBornologyTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CauchyBornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyBornologyTasteGate_single_carrier_alignment_fields
  field_faithful := CauchyBornologyTasteGate_single_carrier_alignment_field_faithful

theorem CauchyBornologyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CauchyBornologyTasteGate_single_carrier_alignment_decodeBHist
          (CauchyBornologyTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CauchyBornologyTasteGate_single_carrier_alignment_fields
          (CauchyBornologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨CauchyBornologyTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CauchyBornologyUp
