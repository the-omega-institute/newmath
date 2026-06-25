import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PartitionCoreIncidenceCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PartitionCoreIncidenceCertificateUp : Type where
  | mk (B Q A L S E R H C P N : BHist) : PartitionCoreIncidenceCertificateUp
  deriving DecidableEq

def partitionCoreIncidenceCertificateEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: partitionCoreIncidenceCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: partitionCoreIncidenceCertificateEncodeBHist h

def partitionCoreIncidenceCertificateDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (partitionCoreIncidenceCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (partitionCoreIncidenceCertificateDecodeBHist tail)

private theorem PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def partitionCoreIncidenceCertificateFields :
    PartitionCoreIncidenceCertificateUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PartitionCoreIncidenceCertificateUp.mk B Q A L S E R H C P N =>
      [B, Q, A, L, S, E, R, H, C, P, N]

def partitionCoreIncidenceCertificateToEventFlow :
    PartitionCoreIncidenceCertificateUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (partitionCoreIncidenceCertificateFields x).map
        partitionCoreIncidenceCertificateEncodeBHist

private def partitionCoreIncidenceCertificateEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      partitionCoreIncidenceCertificateEventAtDefault index rest

def partitionCoreIncidenceCertificateFromEventFlow
    (ef : EventFlow) : Option PartitionCoreIncidenceCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PartitionCoreIncidenceCertificateUp.mk
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 0 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 1 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 2 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 3 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 4 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 5 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 6 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 7 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 8 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 9 ef))
      (partitionCoreIncidenceCertificateDecodeBHist
        (partitionCoreIncidenceCertificateEventAtDefault 10 ef)))

private theorem PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_round_trip
    (x : PartitionCoreIncidenceCertificateUp) :
    partitionCoreIncidenceCertificateFromEventFlow
      (partitionCoreIncidenceCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B Q A L S E R H C P N =>
      change
        some
          (PartitionCoreIncidenceCertificateUp.mk
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist B))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist Q))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist A))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist L))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist S))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist E))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist R))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist H))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist C))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist P))
            (partitionCoreIncidenceCertificateDecodeBHist
              (partitionCoreIncidenceCertificateEncodeBHist N))) =
          some (PartitionCoreIncidenceCertificateUp.mk B Q A L S E R H C P N)
      rw [PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode B,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode Q,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode A,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode L,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode S,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode E,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode R,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode H,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode C,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode P,
        PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode N]

private theorem PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_injective
    {x y : PartitionCoreIncidenceCertificateUp} :
    partitionCoreIncidenceCertificateToEventFlow x =
      partitionCoreIncidenceCertificateToEventFlow y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      partitionCoreIncidenceCertificateFromEventFlow
          (partitionCoreIncidenceCertificateToEventFlow x) =
        partitionCoreIncidenceCertificateFromEventFlow
          (partitionCoreIncidenceCertificateToEventFlow y) :=
    congrArg partitionCoreIncidenceCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_round_trip y)))

private theorem PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_fields :
    forall x y : PartitionCoreIncidenceCertificateUp,
      partitionCoreIncidenceCertificateFields x =
        partitionCoreIncidenceCertificateFields y ->
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 Q1 A1 L1 S1 E1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 Q2 A2 L2 S2 E2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance partitionCoreIncidenceCertificateBHistCarrier :
    BHistCarrier PartitionCoreIncidenceCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := partitionCoreIncidenceCertificateToEventFlow
  fromEventFlow := partitionCoreIncidenceCertificateFromEventFlow

instance partitionCoreIncidenceCertificateChapterTasteGate :
    ChapterTasteGate PartitionCoreIncidenceCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      partitionCoreIncidenceCertificateFromEventFlow
        (partitionCoreIncidenceCertificateToEventFlow x) = some x
    exact PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_injective heq)

instance partitionCoreIncidenceCertificateFieldFaithful :
    FieldFaithful PartitionCoreIncidenceCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := partitionCoreIncidenceCertificateFields
  field_faithful :=
    PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_fields

instance partitionCoreIncidenceCertificateNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PartitionCoreIncidenceCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PartitionCoreIncidenceCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      PartitionCoreIncidenceCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate PartitionCoreIncidenceCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  partitionCoreIncidenceCertificateChapterTasteGate

theorem PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment
    (B Q A L S E R H C P N : BHist) :
    partitionCoreIncidenceCertificateDecodeBHist
        (BMark.b0 :: partitionCoreIncidenceCertificateEncodeBHist B) =
      BHist.e0 B ∧
    partitionCoreIncidenceCertificateFromEventFlow
        (partitionCoreIncidenceCertificateToEventFlow
          (PartitionCoreIncidenceCertificateUp.mk B Q A L S E R H C P N)) =
      some (PartitionCoreIncidenceCertificateUp.mk B Q A L S E R H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact congrArg BHist.e0
      (PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_decode_encode B)
  · exact PartitionCoreIncidenceCertificateTasteGate_single_carrier_alignment_round_trip
      (PartitionCoreIncidenceCertificateUp.mk B Q A L S E R H C P N)

end BEDC.Derived.PartitionCoreIncidenceCertificateUp
