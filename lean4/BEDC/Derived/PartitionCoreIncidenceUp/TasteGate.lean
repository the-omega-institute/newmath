import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PartitionCoreIncidenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PartitionCoreIncidenceUp : Type where
  | mk
      (partition graph support matroid boundary kernel basis transport replay classifier
        routes provenance name : BHist) :
      PartitionCoreIncidenceUp
  deriving DecidableEq

def partitionCoreIncidenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: partitionCoreIncidenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: partitionCoreIncidenceEncodeBHist h

def partitionCoreIncidenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (partitionCoreIncidenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (partitionCoreIncidenceDecodeBHist tail)

private theorem PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def partitionCoreIncidenceFields : PartitionCoreIncidenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PartitionCoreIncidenceUp.mk partition graph support matroid boundary kernel basis transport
      replay classifier routes provenance name =>
      [partition, graph, support, matroid, boundary, kernel, basis, transport, replay,
        classifier, routes, provenance, name]

def partitionCoreIncidenceToEventFlow : PartitionCoreIncidenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (partitionCoreIncidenceFields x).map partitionCoreIncidenceEncodeBHist

private def partitionCoreIncidenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => partitionCoreIncidenceEventAtDefault index rest

def partitionCoreIncidenceFromEventFlow (ef : EventFlow) : Option PartitionCoreIncidenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PartitionCoreIncidenceUp.mk
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 0 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 1 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 2 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 3 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 4 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 5 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 6 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 7 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 8 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 9 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 10 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 11 ef))
      (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEventAtDefault 12 ef)))

private theorem PartitionCoreIncidenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PartitionCoreIncidenceUp,
      partitionCoreIncidenceFromEventFlow (partitionCoreIncidenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk partition graph support matroid boundary kernel basis transport replay classifier routes
      provenance name =>
      change
        some
          (PartitionCoreIncidenceUp.mk
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist partition))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist graph))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist support))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist matroid))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist boundary))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist kernel))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist basis))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist transport))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist replay))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist classifier))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist routes))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist provenance))
            (partitionCoreIncidenceDecodeBHist (partitionCoreIncidenceEncodeBHist name))) =
          some
            (PartitionCoreIncidenceUp.mk partition graph support matroid boundary kernel basis
              transport replay classifier routes provenance name)
      rw [PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode partition,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode graph,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode support,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode matroid,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode boundary,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode kernel,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode basis,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode transport,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode replay,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode classifier,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode routes,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode provenance,
        PartitionCoreIncidenceTasteGate_single_carrier_alignment_decode name]

private theorem PartitionCoreIncidenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PartitionCoreIncidenceUp} :
    partitionCoreIncidenceToEventFlow x = partitionCoreIncidenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      partitionCoreIncidenceFromEventFlow (partitionCoreIncidenceToEventFlow x) =
        partitionCoreIncidenceFromEventFlow (partitionCoreIncidenceToEventFlow y) :=
    congrArg partitionCoreIncidenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PartitionCoreIncidenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PartitionCoreIncidenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem PartitionCoreIncidenceTasteGate_single_carrier_alignment_fields :
    ∀ x y : PartitionCoreIncidenceUp,
      partitionCoreIncidenceFields x = partitionCoreIncidenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk partition1 graph1 support1 matroid1 boundary1 kernel1 basis1 transport1 replay1
      classifier1 routes1 provenance1 name1 =>
      cases y with
      | mk partition2 graph2 support2 matroid2 boundary2 kernel2 basis2 transport2 replay2
          classifier2 routes2 provenance2 name2 =>
          cases hfields
          rfl

instance partitionCoreIncidenceBHistCarrier : BHistCarrier PartitionCoreIncidenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := partitionCoreIncidenceToEventFlow
  fromEventFlow := partitionCoreIncidenceFromEventFlow

instance partitionCoreIncidenceChapterTasteGate : ChapterTasteGate PartitionCoreIncidenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change partitionCoreIncidenceFromEventFlow (partitionCoreIncidenceToEventFlow x) = some x
    exact PartitionCoreIncidenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PartitionCoreIncidenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance partitionCoreIncidenceFieldFaithful : FieldFaithful PartitionCoreIncidenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := partitionCoreIncidenceFields
  field_faithful := PartitionCoreIncidenceTasteGate_single_carrier_alignment_fields

instance partitionCoreIncidenceNontrivial : Nontrivial PartitionCoreIncidenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PartitionCoreIncidenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PartitionCoreIncidenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PartitionCoreIncidenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  partitionCoreIncidenceChapterTasteGate

theorem PartitionCoreIncidenceTasteGate_single_carrier_alignment :
    Nonempty (Nontrivial PartitionCoreIncidenceUp) ∧
      Nonempty (FieldFaithful PartitionCoreIncidenceUp) ∧
        Nonempty (ChapterTasteGate PartitionCoreIncidenceUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨partitionCoreIncidenceNontrivial⟩, ⟨partitionCoreIncidenceFieldFaithful⟩,
      ⟨partitionCoreIncidenceChapterTasteGate⟩⟩

end BEDC.Derived.PartitionCoreIncidenceUp
