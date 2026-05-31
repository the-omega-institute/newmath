import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformModulusTransferUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformModulusTransferUp : Type where
  | mk
      (compact compactMetric continuity stream readback dyadic transfer transport replay
        provenance localCert : BHist) :
      CompactUniformModulusTransferUp
  deriving DecidableEq

def CompactUniformModulusTransferTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: CompactUniformModulusTransferTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: CompactUniformModulusTransferTasteGate_single_carrier_alignment_encodeBHist h

def CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CompactUniformModulusTransferTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CompactUniformModulusTransferTasteGate_single_carrier_alignment_fields :
    CompactUniformModulusTransferUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformModulusTransferUp.mk compact compactMetric continuity stream readback dyadic
      transfer transport replay provenance localCert =>
      [compact, compactMetric, continuity, stream, readback, dyadic, transfer, transport,
        replay, provenance, localCert]

def CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow :
    CompactUniformModulusTransferUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CompactUniformModulusTransferTasteGate_single_carrier_alignment_fields x).map
      CompactUniformModulusTransferTasteGate_single_carrier_alignment_encodeBHist

def CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CompactUniformModulusTransferUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | compact :: compactMetric :: continuity :: stream :: readback :: dyadic :: transfer ::
      transport :: replay :: provenance :: localCert :: [] =>
      some
        (CompactUniformModulusTransferUp.mk
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist compact)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
            compactMetric)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
            continuity)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist stream)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
            readback)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist dyadic)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
            transfer)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
            transport)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist replay)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
            provenance)
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
            localCert))
  | _ => none

private theorem CompactUniformModulusTransferTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformModulusTransferUp,
      CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk compact compactMetric continuity stream readback dyadic transfer transport replay
      provenance localCert =>
      simp only [CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow,
        CompactUniformModulusTransferTasteGate_single_carrier_alignment_fields,
        CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow,
        List.map_cons, List.map_nil,
        CompactUniformModulusTransferTasteGate_single_carrier_alignment_decode_encode]

private theorem CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactUniformModulusTransferUp} :
    CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow x =
        CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow
            (CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow x) :=
        (CompactUniformModulusTransferTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow
            (CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y :=
        CompactUniformModulusTransferTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem CompactUniformModulusTransferTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CompactUniformModulusTransferUp,
      CompactUniformModulusTransferTasteGate_single_carrier_alignment_fields x =
          CompactUniformModulusTransferTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk compact₁ compactMetric₁ continuity₁ stream₁ readback₁ dyadic₁ transfer₁ transport₁
      replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk compact₂ compactMetric₂ continuity₂ stream₂ readback₂ dyadic₂ transfer₂ transport₂
          replay₂ provenance₂ localCert₂ =>
          cases hfields
          rfl

instance CompactUniformModulusTransferTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CompactUniformModulusTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow

instance CompactUniformModulusTransferTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CompactUniformModulusTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CompactUniformModulusTransferTasteGate_single_carrier_alignment_fromEventFlow
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CompactUniformModulusTransferTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactUniformModulusTransferTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CompactUniformModulusTransferTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CompactUniformModulusTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CompactUniformModulusTransferTasteGate_single_carrier_alignment_fields
  field_faithful :=
    CompactUniformModulusTransferTasteGate_single_carrier_alignment_field_faithful

instance CompactUniformModulusTransferTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial CompactUniformModulusTransferUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformModulusTransferUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformModulusTransferUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def CompactUniformModulusTransferTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CompactUniformModulusTransferUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CompactUniformModulusTransferTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CompactUniformModulusTransferTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CompactUniformModulusTransferTasteGate_single_carrier_alignment_decodeBHist
          (CompactUniformModulusTransferTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CompactUniformModulusTransferTasteGate_single_carrier_alignment_fields
          (CompactUniformModulusTransferUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactUniformModulusTransferTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CompactUniformModulusTransferUp
