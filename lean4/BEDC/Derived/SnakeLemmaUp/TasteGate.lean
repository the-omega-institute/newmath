import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SnakeLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SnakeLemmaUp : Type where
  | mk
      (abelianSource upperExact lowerExact vertical kernel cokernel exactness boundary
        transport replay provenance name : BHist) :
      SnakeLemmaUp
  deriving DecidableEq

def snakeLemmaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: snakeLemmaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: snakeLemmaEncodeBHist h

def snakeLemmaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (snakeLemmaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (snakeLemmaDecodeBHist tail)

private theorem SnakeLemmaTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, snakeLemmaDecodeBHist (snakeLemmaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def snakeLemmaFields : SnakeLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SnakeLemmaUp.mk abelianSource upperExact lowerExact vertical kernel cokernel exactness
      boundary transport replay provenance name =>
      [abelianSource, upperExact, lowerExact, vertical, kernel, cokernel, exactness,
        boundary, transport, replay, provenance, name]

def snakeLemmaToEventFlow : SnakeLemmaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (snakeLemmaFields x).map snakeLemmaEncodeBHist

private def snakeLemmaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => snakeLemmaEventAt index rest

def snakeLemmaFromEventFlow (eventFlow : EventFlow) : Option SnakeLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SnakeLemmaUp.mk
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 0 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 1 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 2 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 3 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 4 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 5 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 6 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 7 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 8 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 9 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 10 eventFlow))
      (snakeLemmaDecodeBHist (snakeLemmaEventAt 11 eventFlow)))

private theorem SnakeLemmaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SnakeLemmaUp, snakeLemmaFromEventFlow (snakeLemmaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk abelianSource upperExact lowerExact vertical kernel cokernel exactness boundary
      transport replay provenance name =>
      change
        some
            (SnakeLemmaUp.mk
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist abelianSource))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist upperExact))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist lowerExact))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist vertical))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist kernel))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist cokernel))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist exactness))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist boundary))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist transport))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist replay))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist provenance))
              (snakeLemmaDecodeBHist (snakeLemmaEncodeBHist name))) =
          some
            (SnakeLemmaUp.mk abelianSource upperExact lowerExact vertical kernel cokernel
              exactness boundary transport replay provenance name)
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode abelianSource]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode upperExact]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode lowerExact]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode vertical]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode kernel]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode cokernel]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode exactness]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode boundary]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode transport]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode replay]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode provenance]
      rw [SnakeLemmaTasteGate_single_carrier_alignment_decode name]

private theorem SnakeLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SnakeLemmaUp} :
    snakeLemmaToEventFlow x = snakeLemmaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      snakeLemmaFromEventFlow (snakeLemmaToEventFlow x) =
        snakeLemmaFromEventFlow (snakeLemmaToEventFlow y) :=
    congrArg snakeLemmaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SnakeLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SnakeLemmaTasteGate_single_carrier_alignment_round_trip y)))

private theorem SnakeLemmaTasteGate_single_carrier_alignment_fields :
    ∀ x y : SnakeLemmaUp, snakeLemmaFields x = snakeLemmaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk abelianSource1 upperExact1 lowerExact1 vertical1 kernel1 cokernel1 exactness1
      boundary1 transport1 replay1 provenance1 name1 =>
      cases y with
      | mk abelianSource2 upperExact2 lowerExact2 vertical2 kernel2 cokernel2 exactness2
          boundary2 transport2 replay2 provenance2 name2 =>
          cases hfields
          rfl

instance snakeLemmaBHistCarrier : BHistCarrier SnakeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := snakeLemmaToEventFlow
  fromEventFlow := snakeLemmaFromEventFlow

instance snakeLemmaChapterTasteGate : ChapterTasteGate SnakeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change snakeLemmaFromEventFlow (snakeLemmaToEventFlow x) = some x
    exact SnakeLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SnakeLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance snakeLemmaFieldFaithful : FieldFaithful SnakeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := snakeLemmaFields
  field_faithful := SnakeLemmaTasteGate_single_carrier_alignment_fields

instance snakeLemmaNontrivial : Nontrivial SnakeLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SnakeLemmaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SnakeLemmaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SnakeLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  snakeLemmaChapterTasteGate

theorem SnakeLemmaTasteGate_single_carrier_alignment :
    (∀ h : BHist, snakeLemmaDecodeBHist (snakeLemmaEncodeBHist h) = h) ∧
      (∀ x : SnakeLemmaUp, snakeLemmaFromEventFlow (snakeLemmaToEventFlow x) = some x) ∧
        (∀ x y : SnakeLemmaUp, snakeLemmaToEventFlow x = snakeLemmaToEventFlow y → x = y) ∧
          snakeLemmaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SnakeLemmaTasteGate_single_carrier_alignment_decode,
      SnakeLemmaTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SnakeLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SnakeLemmaUp
