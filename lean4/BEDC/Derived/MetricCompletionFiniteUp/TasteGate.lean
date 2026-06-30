import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionFiniteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionFiniteUp : Type where
  | mk (M B W E R S H C P N : BHist) : MetricCompletionFiniteUp
  deriving DecidableEq

def metricCompletionFiniteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionFiniteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionFiniteEncodeBHist h

def metricCompletionFiniteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionFiniteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionFiniteDecodeBHist tail)

private theorem metricCompletionFiniteDecodeEncode :
    ∀ h : BHist, metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricCompletionFiniteFields : MetricCompletionFiniteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionFiniteUp.mk M B W E R S H C P N => [M, B, W, E, R, S, H, C, P, N]

def metricCompletionFiniteToEventFlow : MetricCompletionFiniteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricCompletionFiniteFields x).map metricCompletionFiniteEncodeBHist

private def metricCompletionFiniteEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricCompletionFiniteEventAtDefault index rest

def metricCompletionFiniteFromEventFlow : EventFlow → Option MetricCompletionFiniteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MetricCompletionFiniteUp.mk
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 0 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 1 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 2 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 3 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 4 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 5 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 6 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 7 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 8 ef))
        (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEventAtDefault 9 ef)))

private theorem metricCompletionFiniteRoundTrip :
    ∀ x : MetricCompletionFiniteUp,
      metricCompletionFiniteFromEventFlow (metricCompletionFiniteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M B W E R S H C P N =>
      change
        some
          (MetricCompletionFiniteUp.mk
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist M))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist B))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist W))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist E))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist R))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist S))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist H))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist C))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist P))
            (metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist N))) =
          some (MetricCompletionFiniteUp.mk M B W E R S H C P N)
      rw [metricCompletionFiniteDecodeEncode M, metricCompletionFiniteDecodeEncode B,
        metricCompletionFiniteDecodeEncode W, metricCompletionFiniteDecodeEncode E,
        metricCompletionFiniteDecodeEncode R, metricCompletionFiniteDecodeEncode S,
        metricCompletionFiniteDecodeEncode H, metricCompletionFiniteDecodeEncode C,
        metricCompletionFiniteDecodeEncode P, metricCompletionFiniteDecodeEncode N]

private theorem metricCompletionFiniteToEventFlow_injective
    {x y : MetricCompletionFiniteUp} :
    metricCompletionFiniteToEventFlow x = metricCompletionFiniteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricCompletionFiniteFromEventFlow (metricCompletionFiniteToEventFlow x) =
        metricCompletionFiniteFromEventFlow (metricCompletionFiniteToEventFlow y) :=
    congrArg metricCompletionFiniteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricCompletionFiniteRoundTrip x).symm
      (Eq.trans hread (metricCompletionFiniteRoundTrip y)))

instance metricCompletionFiniteBHistCarrier : BHistCarrier MetricCompletionFiniteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionFiniteToEventFlow
  fromEventFlow := metricCompletionFiniteFromEventFlow

instance metricCompletionFiniteChapterTasteGate : ChapterTasteGate MetricCompletionFiniteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricCompletionFiniteFromEventFlow (metricCompletionFiniteToEventFlow x) = some x
    exact metricCompletionFiniteRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricCompletionFiniteToEventFlow_injective heq)

theorem MetricCompletionFiniteTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist h) = h) ∧
      (∀ x : MetricCompletionFiniteUp,
        metricCompletionFiniteFromEventFlow (metricCompletionFiniteToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier MetricCompletionFiniteUp) ∧
        Nonempty (ChapterTasteGate MetricCompletionFiniteUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨metricCompletionFiniteDecodeEncode,
      metricCompletionFiniteRoundTrip,
      ⟨metricCompletionFiniteBHistCarrier⟩,
      ⟨metricCompletionFiniteChapterTasteGate⟩⟩

theorem MetricCompletionFiniteNameCertObligations (M B W E R S H C P N : BHist) :
    metricCompletionFiniteFields (MetricCompletionFiniteUp.mk M B W E R S H C P N) =
        [M, B, W, E, R, S, H, C, P, N] ∧
      metricCompletionFiniteEncodeBHist BHist.Empty = ([] : List BMark) ∧
        metricCompletionFiniteDecodeBHist (metricCompletionFiniteEncodeBHist M) = M := by
  -- BEDC touchpoint anchor: BHist BMark NameCert
  exact ⟨rfl, rfl, metricCompletionFiniteDecodeEncode M⟩

end BEDC.Derived.MetricCompletionFiniteUp
