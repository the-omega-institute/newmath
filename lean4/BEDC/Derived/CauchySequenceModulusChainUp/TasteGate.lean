import BEDC.Derived.CauchySequenceModulusChainUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceModulusChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchySequenceModulusChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceModulusChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceModulusChainEncodeBHist h

def cauchySequenceModulusChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceModulusChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceModulusChainDecodeBHist tail)

private theorem cauchySequenceModulusChainDecode_encode :
    ∀ h : BHist,
      cauchySequenceModulusChainDecodeBHist (cauchySequenceModulusChainEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceModulusChainToEventFlow : CauchySequenceModulusChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySequenceModulusChainUp.mk streamWindow regSeqReadback dyadicTolerance
      modulusChain realSeal transport replay provenance name =>
      [cauchySequenceModulusChainEncodeBHist streamWindow,
        cauchySequenceModulusChainEncodeBHist regSeqReadback,
        cauchySequenceModulusChainEncodeBHist dyadicTolerance,
        cauchySequenceModulusChainEncodeBHist modulusChain,
        cauchySequenceModulusChainEncodeBHist realSeal,
        cauchySequenceModulusChainEncodeBHist transport,
        cauchySequenceModulusChainEncodeBHist replay,
        cauchySequenceModulusChainEncodeBHist provenance,
        cauchySequenceModulusChainEncodeBHist name]

private def cauchySequenceModulusChainEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceModulusChainEventAtDefault index rest

def cauchySequenceModulusChainFromEventFlow :
    EventFlow → Option CauchySequenceModulusChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchySequenceModulusChainUp.mk
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 0 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 1 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 2 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 3 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 4 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 5 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 6 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 7 ef))
        (cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEventAtDefault 8 ef)))

private theorem cauchySequenceModulusChain_round_trip :
    ∀ x : CauchySequenceModulusChainUp,
      cauchySequenceModulusChainFromEventFlow
        (cauchySequenceModulusChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk streamWindow regSeqReadback dyadicTolerance modulusChain realSeal transport replay
      provenance name =>
      change
        some
          (CauchySequenceModulusChainUp.mk
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist streamWindow))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist regSeqReadback))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist dyadicTolerance))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist modulusChain))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist realSeal))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist transport))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist replay))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist provenance))
            (cauchySequenceModulusChainDecodeBHist
              (cauchySequenceModulusChainEncodeBHist name))) =
          some
            (CauchySequenceModulusChainUp.mk streamWindow regSeqReadback dyadicTolerance
              modulusChain realSeal transport replay provenance name)
      rw [cauchySequenceModulusChainDecode_encode streamWindow,
        cauchySequenceModulusChainDecode_encode regSeqReadback,
        cauchySequenceModulusChainDecode_encode dyadicTolerance,
        cauchySequenceModulusChainDecode_encode modulusChain,
        cauchySequenceModulusChainDecode_encode realSeal,
        cauchySequenceModulusChainDecode_encode transport,
        cauchySequenceModulusChainDecode_encode replay,
        cauchySequenceModulusChainDecode_encode provenance,
        cauchySequenceModulusChainDecode_encode name]

private theorem cauchySequenceModulusChainToEventFlow_injective
    {x y : CauchySequenceModulusChainUp} :
    cauchySequenceModulusChainToEventFlow x =
        cauchySequenceModulusChainToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceModulusChainFromEventFlow
          (cauchySequenceModulusChainToEventFlow x) =
        cauchySequenceModulusChainFromEventFlow
          (cauchySequenceModulusChainToEventFlow y) :=
    congrArg cauchySequenceModulusChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySequenceModulusChain_round_trip x).symm
      (Eq.trans hread (cauchySequenceModulusChain_round_trip y)))

instance cauchySequenceModulusChainBHistCarrier :
    BHistCarrier CauchySequenceModulusChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceModulusChainToEventFlow
  fromEventFlow := cauchySequenceModulusChainFromEventFlow

instance cauchySequenceModulusChainChapterTasteGate :
    ChapterTasteGate CauchySequenceModulusChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchySequenceModulusChainFromEventFlow
          (cauchySequenceModulusChainToEventFlow x) =
        some x
    exact cauchySequenceModulusChain_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceModulusChainToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchySequenceModulusChainUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySequenceModulusChainChapterTasteGate

theorem CauchySequenceModulusChainTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchySequenceModulusChainDecodeBHist
          (cauchySequenceModulusChainEncodeBHist h) = h) ∧
      (∀ x : CauchySequenceModulusChainUp,
        cauchySequenceModulusChainFromEventFlow
            (cauchySequenceModulusChainToEventFlow x) = some x) ∧
        (∀ x y : CauchySequenceModulusChainUp,
          cauchySequenceModulusChainToEventFlow x =
              cauchySequenceModulusChainToEventFlow y →
            x = y) ∧
          cauchySequenceModulusChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchySequenceModulusChainDecode_encode,
      cauchySequenceModulusChain_round_trip,
      (fun _ _ heq => cauchySequenceModulusChainToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchySequenceModulusChainUp
