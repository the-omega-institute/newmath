import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorFanBarrierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorFanBarrierUp : Type where
  | mk
      (fan address barrier depth witness stream readback realSeal transport classifier
        provenance name : BHist) :
      CantorFanBarrierUp
  deriving DecidableEq

def CantorFanBarrierTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CantorFanBarrierTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CantorFanBarrierTasteGate_single_carrier_alignment_encodeBHist h

def CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CantorFanBarrierTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist
          (CantorFanBarrierTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CantorFanBarrierTasteGate_single_carrier_alignment_fields :
    CantorFanBarrierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorFanBarrierUp.mk fan address barrier depth witness stream readback realSeal transport
      classifier provenance name =>
      [fan, address, barrier, depth, witness, stream, readback, realSeal, transport,
        classifier, provenance, name]

def CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow :
    CantorFanBarrierUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CantorFanBarrierTasteGate_single_carrier_alignment_fields x).map
      CantorFanBarrierTasteGate_single_carrier_alignment_encodeBHist

def CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CantorFanBarrierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | fan :: address :: barrier :: depth :: witness :: stream :: readback :: realSeal ::
      transport :: classifier :: provenance :: name :: [] =>
      some
        (CantorFanBarrierUp.mk
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist fan)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist address)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist barrier)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist depth)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist witness)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist stream)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist readback)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist realSeal)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist transport)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist classifier)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist provenance)
          (CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist name))
  | _ => none

private theorem CantorFanBarrierTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CantorFanBarrierUp,
      CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow
          (CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk fan address barrier depth witness stream readback realSeal transport classifier
      provenance name =>
      simp only [CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow,
        CantorFanBarrierTasteGate_single_carrier_alignment_fields,
        CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, CantorFanBarrierTasteGate_single_carrier_alignment_decode_encode]

private theorem CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CantorFanBarrierUp} :
    CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow x =
        CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow
            (CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CantorFanBarrierTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow
            (CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := CantorFanBarrierTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem CantorFanBarrierTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CantorFanBarrierUp,
      CantorFanBarrierTasteGate_single_carrier_alignment_fields x =
          CantorFanBarrierTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk fan1 address1 barrier1 depth1 witness1 stream1 readback1 realSeal1 transport1
      classifier1 provenance1 name1 =>
      cases y with
      | mk fan2 address2 barrier2 depth2 witness2 stream2 readback2 realSeal2 transport2
          classifier2 provenance2 name2 =>
          cases hfields
          rfl

instance CantorFanBarrierTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CantorFanBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow

instance CantorFanBarrierTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CantorFanBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CantorFanBarrierTasteGate_single_carrier_alignment_fromEventFlow
          (CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CantorFanBarrierTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorFanBarrierTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CantorFanBarrierTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CantorFanBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CantorFanBarrierTasteGate_single_carrier_alignment_fields
  field_faithful := CantorFanBarrierTasteGate_single_carrier_alignment_field_faithful

instance CantorFanBarrierTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial CantorFanBarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CantorFanBarrierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CantorFanBarrierUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def CantorFanBarrierTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CantorFanBarrierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CantorFanBarrierTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CantorFanBarrierTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CantorFanBarrierTasteGate_single_carrier_alignment_decodeBHist
          (CantorFanBarrierTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CantorFanBarrierTasteGate_single_carrier_alignment_fields
          (CantorFanBarrierUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨CantorFanBarrierTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CantorFanBarrierUp
