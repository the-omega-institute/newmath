import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BornologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BornologyUp : Type where
  | mk (boundedFamily subsetHeredity finiteUnion sourceExposure consumerHandoff transport
      replay provenance localName : BHist) : BornologyUp
  deriving DecidableEq

def bornologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bornologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bornologyEncodeBHist h

def bornologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bornologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bornologyDecodeBHist tail)

private theorem BornologyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bornologyDecodeBHist (bornologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BornologyTasteGate_single_carrier_alignment_fields :
    BornologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BornologyUp.mk boundedFamily subsetHeredity finiteUnion sourceExposure consumerHandoff
      transport replay provenance localName =>
      [boundedFamily, subsetHeredity, finiteUnion, sourceExposure, consumerHandoff, transport,
        replay, provenance, localName]

def BornologyTasteGate_single_carrier_alignment_toEventFlow :
    BornologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BornologyTasteGate_single_carrier_alignment_fields x).map bornologyEncodeBHist

def BornologyTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | boundedFamily :: subsetHeredity :: finiteUnion :: sourceExposure :: consumerHandoff ::
        transport :: replay :: provenance :: localName :: [] =>
      some
        (BornologyUp.mk
          (bornologyDecodeBHist boundedFamily)
          (bornologyDecodeBHist subsetHeredity)
          (bornologyDecodeBHist finiteUnion)
          (bornologyDecodeBHist sourceExposure)
          (bornologyDecodeBHist consumerHandoff)
          (bornologyDecodeBHist transport)
          (bornologyDecodeBHist replay)
          (bornologyDecodeBHist provenance)
          (bornologyDecodeBHist localName))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def BornologyTasteGate_single_carrier_alignment_carrier :
    BHistCarrier BornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BornologyTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BornologyTasteGate_single_carrier_alignment_fromEventFlow

instance BornologyTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BornologyTasteGate_single_carrier_alignment_carrier

private theorem BornologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BornologyUp,
      BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk boundedFamily subsetHeredity finiteUnion sourceExposure consumerHandoff transport replay
      provenance localName =>
      change
        some
            (BornologyUp.mk
              (bornologyDecodeBHist (bornologyEncodeBHist boundedFamily))
              (bornologyDecodeBHist (bornologyEncodeBHist subsetHeredity))
              (bornologyDecodeBHist (bornologyEncodeBHist finiteUnion))
              (bornologyDecodeBHist (bornologyEncodeBHist sourceExposure))
              (bornologyDecodeBHist (bornologyEncodeBHist consumerHandoff))
              (bornologyDecodeBHist (bornologyEncodeBHist transport))
              (bornologyDecodeBHist (bornologyEncodeBHist replay))
              (bornologyDecodeBHist (bornologyEncodeBHist provenance))
              (bornologyDecodeBHist (bornologyEncodeBHist localName))) =
          some
            (BornologyUp.mk boundedFamily subsetHeredity finiteUnion sourceExposure
              consumerHandoff transport replay provenance localName)
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode boundedFamily]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode subsetHeredity]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode finiteUnion]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode sourceExposure]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode consumerHandoff]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode transport]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode replay]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode provenance]
      rw [BornologyTasteGate_single_carrier_alignment_decode_encode localName]

private theorem BornologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BornologyUp} :
    BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) :=
        (BornologyTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow y) :=
        congrArg BHistCarrier.fromEventFlow hxy
      _ = some y := BornologyTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem BornologyTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BornologyUp,
      BornologyTasteGate_single_carrier_alignment_fields x =
          BornologyTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk boundedFamily₁ subsetHeredity₁ finiteUnion₁ sourceExposure₁ consumerHandoff₁
      transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk boundedFamily₂ subsetHeredity₂ finiteUnion₂ sourceExposure₂ consumerHandoff₂
          transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

def BornologyTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate BornologyUp BornologyTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact BornologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BornologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance BornologyTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BornologyTasteGate_single_carrier_alignment_gate

instance BornologyTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful BornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BornologyTasteGate_single_carrier_alignment_fields
  field_faithful := BornologyTasteGate_single_carrier_alignment_field_faithful

theorem BornologyTasteGate_single_carrier_alignment :
    (forall h : BHist, bornologyDecodeBHist (bornologyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BornologyUp) ∧
      Nonempty (ChapterTasteGate BornologyUp) ∧
      bornologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BornologyTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨BornologyTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨BornologyTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.BornologyUp
