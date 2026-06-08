import BEDC.Derived.MetricEntourageUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricEntourageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def metricEntourageEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricEntourageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricEntourageEncodeBHist h

def metricEntourageDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricEntourageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricEntourageDecodeBHist tail)

private theorem MetricEntourageTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, metricEntourageDecodeBHist (metricEntourageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricEntourageToEventFlow : MetricEntourageUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricEntourageUp.mk M Q D B S T H C P N =>
      [metricEntourageEncodeBHist M,
        metricEntourageEncodeBHist Q,
        metricEntourageEncodeBHist D,
        metricEntourageEncodeBHist B,
        metricEntourageEncodeBHist S,
        metricEntourageEncodeBHist T,
        metricEntourageEncodeBHist H,
        metricEntourageEncodeBHist C,
        metricEntourageEncodeBHist P,
        metricEntourageEncodeBHist N]

private def metricEntourageEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricEntourageEventAtDefault index rest

def metricEntourageFromEventFlow (ef : EventFlow) : Option MetricEntourageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricEntourageUp.mk
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 0 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 1 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 2 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 3 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 4 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 5 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 6 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 7 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 8 ef))
      (metricEntourageDecodeBHist (metricEntourageEventAtDefault 9 ef)))

private theorem MetricEntourageTasteGate_single_carrier_alignment_round_trip
    (x : MetricEntourageUp) :
    metricEntourageFromEventFlow (metricEntourageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M Q D B S T H C P N =>
      change
        some
          (MetricEntourageUp.mk
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist M))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist Q))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist D))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist B))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist S))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist T))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist H))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist C))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist P))
            (metricEntourageDecodeBHist (metricEntourageEncodeBHist N))) =
          some (MetricEntourageUp.mk M Q D B S T H C P N)
      rw [MetricEntourageTasteGate_single_carrier_alignment_decode M,
        MetricEntourageTasteGate_single_carrier_alignment_decode Q,
        MetricEntourageTasteGate_single_carrier_alignment_decode D,
        MetricEntourageTasteGate_single_carrier_alignment_decode B,
        MetricEntourageTasteGate_single_carrier_alignment_decode S,
        MetricEntourageTasteGate_single_carrier_alignment_decode T,
        MetricEntourageTasteGate_single_carrier_alignment_decode H,
        MetricEntourageTasteGate_single_carrier_alignment_decode C,
        MetricEntourageTasteGate_single_carrier_alignment_decode P,
        MetricEntourageTasteGate_single_carrier_alignment_decode N]

private theorem MetricEntourageTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MetricEntourageUp} :
    metricEntourageToEventFlow x = metricEntourageToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricEntourageFromEventFlow (metricEntourageToEventFlow x) =
        metricEntourageFromEventFlow (metricEntourageToEventFlow y) :=
    congrArg metricEntourageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MetricEntourageTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MetricEntourageTasteGate_single_carrier_alignment_round_trip y)))

instance metricEntourageBHistCarrier : BHistCarrier MetricEntourageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricEntourageToEventFlow
  fromEventFlow := metricEntourageFromEventFlow

instance metricEntourageChapterTasteGate : ChapterTasteGate MetricEntourageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricEntourageFromEventFlow (metricEntourageToEventFlow x) = some x
    exact MetricEntourageTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetricEntourageTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MetricEntourageTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricEntourageDecodeBHist (metricEntourageEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricEntourageUp) ∧
        Nonempty (ChapterTasteGate MetricEntourageUp) ∧
          metricEntourageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨MetricEntourageTasteGate_single_carrier_alignment_decode,
      ⟨metricEntourageBHistCarrier⟩,
      ⟨metricEntourageChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetricEntourageUp
