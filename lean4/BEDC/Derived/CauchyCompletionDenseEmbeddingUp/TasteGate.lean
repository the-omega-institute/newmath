import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionDenseEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionDenseEmbeddingUp : Type where
  | mk (denseSource embeddingGraph completion streamWindow dyadicTolerance regularReadback
      realSeal transport replay provenance localName : BHist) :
      CauchyCompletionDenseEmbeddingUp
  deriving DecidableEq

def cauchyCompletionDenseEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionDenseEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionDenseEmbeddingEncodeBHist h

def cauchyCompletionDenseEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionDenseEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionDenseEmbeddingDecodeBHist tail)

private theorem CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionDenseEmbeddingDecodeBHist
        (cauchyCompletionDenseEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fields :
    CauchyCompletionDenseEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionDenseEmbeddingUp.mk denseSource embeddingGraph completion streamWindow
      dyadicTolerance regularReadback realSeal transport replay provenance localName =>
      [denseSource, embeddingGraph, completion, streamWindow, dyadicTolerance, regularReadback,
        realSeal, transport, replay, provenance, localName]

def CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow :
    CauchyCompletionDenseEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fields x).map
      cauchyCompletionDenseEmbeddingEncodeBHist

private def CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt index rest

def CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CauchyCompletionDenseEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    some
      (CauchyCompletionDenseEmbeddingUp.mk
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 0 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 1 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 2 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 3 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 4 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 5 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 6 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 7 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 8 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 9 eventFlow))
        (cauchyCompletionDenseEmbeddingDecodeBHist
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_rawAt 10 eventFlow)))

private theorem CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionDenseEmbeddingUp,
      CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk denseSource embeddingGraph completion streamWindow dyadicTolerance regularReadback
      realSeal transport replay provenance localName =>
      change
        some
            (CauchyCompletionDenseEmbeddingUp.mk
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist denseSource))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist embeddingGraph))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist completion))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist streamWindow))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist dyadicTolerance))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist regularReadback))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist realSeal))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist transport))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist replay))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist provenance))
              (cauchyCompletionDenseEmbeddingDecodeBHist
                (cauchyCompletionDenseEmbeddingEncodeBHist localName))) =
          some
            (CauchyCompletionDenseEmbeddingUp.mk denseSource embeddingGraph completion
              streamWindow dyadicTolerance regularReadback realSeal transport replay provenance
              localName)
      rw [CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode denseSource,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode embeddingGraph,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode completion,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode streamWindow,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode dyadicTolerance,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode regularReadback,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode realSeal,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionDenseEmbeddingUp} :
    CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow x =
      CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_round_trip y)))

instance CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyCompletionDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyCompletionDenseEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionDenseEmbeddingDecodeBHist
        (cauchyCompletionDenseEmbeddingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionDenseEmbeddingUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionDenseEmbeddingUp) ∧
          cauchyCompletionDenseEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_decode_encode,
      ⟨CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_BHistCarrier⟩,
      ⟨CauchyCompletionDenseEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionDenseEmbeddingUp
