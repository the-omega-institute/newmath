import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FinitePartitionMeshUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FinitePartitionMeshUp : Type where
  | mk :
      (interval dyadic window readback mesh refinement darbouxPartition darbouxSum transport
        replay provenance nameCert : BHist) ->
        FinitePartitionMeshUp
  deriving DecidableEq

def finitePartitionMeshEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finitePartitionMeshEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finitePartitionMeshEncodeBHist h

def finitePartitionMeshDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finitePartitionMeshDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finitePartitionMeshDecodeBHist tail)

theorem FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finitePartitionMeshFields : FinitePartitionMeshUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FinitePartitionMeshUp.mk interval dyadic window readback mesh refinement darbouxPartition
      darbouxSum transport replay provenance nameCert =>
      [interval, dyadic, window, readback, mesh, refinement, darbouxPartition, darbouxSum,
        transport, replay, provenance, nameCert]

def finitePartitionMeshToEventFlow : FinitePartitionMeshUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finitePartitionMeshFields x).map finitePartitionMeshEncodeBHist

def finitePartitionMeshFromEventFlow : EventFlow -> Option FinitePartitionMeshUp
  -- BEDC touchpoint anchor: BHist BMark
  | interval :: dyadic :: window :: readback :: mesh :: refinement :: darbouxPartition ::
      darbouxSum :: transport :: replay :: provenance :: nameCert :: [] =>
      some
        (FinitePartitionMeshUp.mk
          (finitePartitionMeshDecodeBHist interval)
          (finitePartitionMeshDecodeBHist dyadic)
          (finitePartitionMeshDecodeBHist window)
          (finitePartitionMeshDecodeBHist readback)
          (finitePartitionMeshDecodeBHist mesh)
          (finitePartitionMeshDecodeBHist refinement)
          (finitePartitionMeshDecodeBHist darbouxPartition)
          (finitePartitionMeshDecodeBHist darbouxSum)
          (finitePartitionMeshDecodeBHist transport)
          (finitePartitionMeshDecodeBHist replay)
          (finitePartitionMeshDecodeBHist provenance)
          (finitePartitionMeshDecodeBHist nameCert))
  | _ => none

private theorem finitePartitionMesh_round_trip :
    forall x : FinitePartitionMeshUp,
      finitePartitionMeshFromEventFlow (finitePartitionMeshToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval dyadic window readback mesh refinement darbouxPartition darbouxSum transport
      replay provenance nameCert =>
      change
        some
          (FinitePartitionMeshUp.mk
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist interval))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist dyadic))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist window))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist readback))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist mesh))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist refinement))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist darbouxPartition))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist darbouxSum))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist transport))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist replay))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist provenance))
            (finitePartitionMeshDecodeBHist (finitePartitionMeshEncodeBHist nameCert))) =
          some
            (FinitePartitionMeshUp.mk interval dyadic window readback mesh refinement
              darbouxPartition darbouxSum transport replay provenance nameCert)
      rw [FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode interval,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode dyadic,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode window,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode readback,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode mesh,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode refinement,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode darbouxPartition,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode darbouxSum,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode transport,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode replay,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode provenance,
        FinitePartitionMeshTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem finitePartitionMesh_toEventFlow_injective
    {x y : FinitePartitionMeshUp} :
    finitePartitionMeshToEventFlow x = finitePartitionMeshToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finitePartitionMeshFromEventFlow (finitePartitionMeshToEventFlow x) =
        finitePartitionMeshFromEventFlow (finitePartitionMeshToEventFlow y) :=
    congrArg finitePartitionMeshFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finitePartitionMesh_round_trip x).symm
      (Eq.trans hread (finitePartitionMesh_round_trip y)))

private theorem finitePartitionMesh_field_faithful :
    forall x y : FinitePartitionMeshUp, finitePartitionMeshFields x = finitePartitionMeshFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk interval₁ dyadic₁ window₁ readback₁ mesh₁ refinement₁ darbouxPartition₁ darbouxSum₁
      transport₁ replay₁ provenance₁ nameCert₁ =>
      cases y with
      | mk interval₂ dyadic₂ window₂ readback₂ mesh₂ refinement₂ darbouxPartition₂
          darbouxSum₂ transport₂ replay₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance finitePartitionMeshBHistCarrier : BHistCarrier FinitePartitionMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finitePartitionMeshToEventFlow
  fromEventFlow := finitePartitionMeshFromEventFlow

instance finitePartitionMeshChapterTasteGate : ChapterTasteGate FinitePartitionMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x => finitePartitionMesh_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finitePartitionMesh_toEventFlow_injective heq)

instance finitePartitionMeshFieldFaithful : FieldFaithful FinitePartitionMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finitePartitionMeshFields
  field_faithful := finitePartitionMesh_field_faithful

instance finitePartitionMeshNontrivial : BEDC.Meta.TasteGate.Nontrivial FinitePartitionMeshUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FinitePartitionMeshUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FinitePartitionMeshUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def finitePartitionMeshTasteGate : ChapterTasteGate FinitePartitionMeshUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finitePartitionMeshChapterTasteGate

end BEDC.Derived.FinitePartitionMeshUp
