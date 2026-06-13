import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricSeparationReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricSeparationReflectorUp : Type where
  | mk (P Z S M C D W Q A H K G N : BHist) : MetricSeparationReflectorUp
  deriving DecidableEq

def metricSeparationReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricSeparationReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricSeparationReflectorEncodeBHist h

def metricSeparationReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricSeparationReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricSeparationReflectorDecodeBHist tail)

private theorem MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricSeparationReflectorToEventFlow : MetricSeparationReflectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricSeparationReflectorUp.mk P Z S M C D W Q A H K G N =>
      ([
        P, Z, S, M, C, D, W, Q, A, H, K, G, N
      ] : List BHist).map metricSeparationReflectorEncodeBHist

private def metricSeparationReflectorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricSeparationReflectorEventAt index rest

def metricSeparationReflectorFromEventFlow (ef : EventFlow) :
    Option MetricSeparationReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricSeparationReflectorUp.mk
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 0 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 1 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 2 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 3 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 4 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 5 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 6 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 7 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 8 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 9 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 10 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 11 ef))
      (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEventAt 12 ef)))

private theorem MetricSeparationReflectorTasteGate_single_carrier_alignment_round_trip
    (x : MetricSeparationReflectorUp) :
    metricSeparationReflectorFromEventFlow (metricSeparationReflectorToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P Z S M C D W Q A H K G N =>
      change
        some
          (MetricSeparationReflectorUp.mk
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist P))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist Z))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist S))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist M))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist C))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist D))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist W))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist Q))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist A))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist H))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist K))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist G))
            (metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist N))) =
          some (MetricSeparationReflectorUp.mk P Z S M C D W Q A H K G N)
      rw [MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode P,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode Z,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode S,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode M,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode C,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode D,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode W,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode Q,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode A,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode H,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode K,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode G,
        MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode N]

private theorem metricSeparationReflectorToEventFlow_injective
    {x y : MetricSeparationReflectorUp} :
    metricSeparationReflectorToEventFlow x = metricSeparationReflectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricSeparationReflectorFromEventFlow (metricSeparationReflectorToEventFlow x) =
        metricSeparationReflectorFromEventFlow (metricSeparationReflectorToEventFlow y) :=
    congrArg metricSeparationReflectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetricSeparationReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MetricSeparationReflectorTasteGate_single_carrier_alignment_round_trip y)))

instance metricSeparationReflectorBHistCarrier : BHistCarrier MetricSeparationReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricSeparationReflectorToEventFlow
  fromEventFlow := metricSeparationReflectorFromEventFlow

instance metricSeparationReflectorChapterTasteGate :
    ChapterTasteGate MetricSeparationReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricSeparationReflectorFromEventFlow (metricSeparationReflectorToEventFlow x) =
      some x
    exact MetricSeparationReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricSeparationReflectorToEventFlow_injective heq)

theorem MetricSeparationReflectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        metricSeparationReflectorDecodeBHist (metricSeparationReflectorEncodeBHist h) = h) ∧
      (∀ x : MetricSeparationReflectorUp,
        metricSeparationReflectorFromEventFlow (metricSeparationReflectorToEventFlow x) =
          some x) ∧
        (∀ x y : MetricSeparationReflectorUp,
          metricSeparationReflectorToEventFlow x = metricSeparationReflectorToEventFlow y ->
            x = y) ∧
          metricSeparationReflectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨MetricSeparationReflectorTasteGate_single_carrier_alignment_decode_encode,
      MetricSeparationReflectorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => metricSeparationReflectorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetricSeparationReflectorUp
