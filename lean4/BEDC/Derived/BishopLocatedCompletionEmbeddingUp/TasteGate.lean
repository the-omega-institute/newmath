import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedCompletionEmbeddingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedCompletionEmbeddingUp : Type where
  | mk (metric located dense embedding readback transport replay provenance name : BHist) :
      BishopLocatedCompletionEmbeddingUp
  deriving DecidableEq

def bishopLocatedCompletionEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedCompletionEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedCompletionEmbeddingEncodeBHist h

def bishopLocatedCompletionEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedCompletionEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedCompletionEmbeddingDecodeBHist tail)

private theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopLocatedCompletionEmbeddingDecodeBHist
          (bishopLocatedCompletionEmbeddingEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedCompletionEmbeddingFields :
    BishopLocatedCompletionEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedCompletionEmbeddingUp.mk metric located dense embedding readback transport
      replay provenance name =>
      [metric, located, dense, embedding, readback, transport, replay, provenance, name]

def bishopLocatedCompletionEmbeddingToEventFlow :
    BishopLocatedCompletionEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (bishopLocatedCompletionEmbeddingFields x).map
        bishopLocatedCompletionEmbeddingEncodeBHist

private def bishopLocatedCompletionEmbeddingEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedCompletionEmbeddingEventAt index rest

def bishopLocatedCompletionEmbeddingFromEventFlow
    (ef : EventFlow) : Option BishopLocatedCompletionEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedCompletionEmbeddingUp.mk
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 0 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 1 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 2 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 3 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 4 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 5 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 6 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 7 ef))
      (bishopLocatedCompletionEmbeddingDecodeBHist
        (bishopLocatedCompletionEmbeddingEventAt 8 ef)))

private theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip
    (x : BishopLocatedCompletionEmbeddingUp) :
    bishopLocatedCompletionEmbeddingFromEventFlow
        (bishopLocatedCompletionEmbeddingToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk metric located dense embedding readback transport replay provenance name =>
      change
        some
          (BishopLocatedCompletionEmbeddingUp.mk
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist metric))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist located))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist dense))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist embedding))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist readback))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist transport))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist replay))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist provenance))
            (bishopLocatedCompletionEmbeddingDecodeBHist
              (bishopLocatedCompletionEmbeddingEncodeBHist name))) =
          some
            (BishopLocatedCompletionEmbeddingUp.mk metric located dense embedding readback
              transport replay provenance name)
      rw [BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode metric,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode located,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode dense,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode embedding,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode readback,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode transport,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode replay,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode provenance,
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode name]

private theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopLocatedCompletionEmbeddingUp} :
    bishopLocatedCompletionEmbeddingToEventFlow x =
        bishopLocatedCompletionEmbeddingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedCompletionEmbeddingFromEventFlow
          (bishopLocatedCompletionEmbeddingToEventFlow x) =
        bishopLocatedCompletionEmbeddingFromEventFlow
          (bishopLocatedCompletionEmbeddingToEventFlow y) :=
    congrArg bishopLocatedCompletionEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedCompletionEmbeddingBHistCarrier :
    BHistCarrier BishopLocatedCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedCompletionEmbeddingToEventFlow
  fromEventFlow := bishopLocatedCompletionEmbeddingFromEventFlow

instance bishopLocatedCompletionEmbeddingChapterTasteGate :
    ChapterTasteGate BishopLocatedCompletionEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedCompletionEmbeddingFromEventFlow
          (bishopLocatedCompletionEmbeddingToEventFlow x) =
        some x
    exact BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate BishopLocatedCompletionEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedCompletionEmbeddingChapterTasteGate

theorem BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedCompletionEmbeddingDecodeBHist
          (bishopLocatedCompletionEmbeddingEncodeBHist h) =
        h) ∧
      (∀ x : BishopLocatedCompletionEmbeddingUp,
        bishopLocatedCompletionEmbeddingFromEventFlow
            (bishopLocatedCompletionEmbeddingToEventFlow x) =
          some x) ∧
        (∀ x y : BishopLocatedCompletionEmbeddingUp,
          bishopLocatedCompletionEmbeddingToEventFlow x =
              bishopLocatedCompletionEmbeddingToEventFlow y →
            x = y) ∧
          bishopLocatedCompletionEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_decode_encode,
      BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopLocatedCompletionEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.BishopLocatedCompletionEmbeddingUp.TasteGate
