import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicMetricUp : Type where
  | mk (X d b t beta q F H C P N : BHist) : HyperbolicMetricUp
  deriving DecidableEq

def hyperbolicMetricEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicMetricEncodeBHist h

def hyperbolicMetricDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicMetricDecodeBHist tail)

private theorem hyperbolicMetric_decode_encode :
    forall h : BHist,
      hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicMetricFields : HyperbolicMetricUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicMetricUp.mk X d b t beta q F H C P N => [X, d, b, t, beta, q, F, H, C, P, N]

def hyperbolicMetricToEventFlow : HyperbolicMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicMetricFields x).map hyperbolicMetricEncodeBHist

private def hyperbolicMetricEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicMetricEventAt index rest

def hyperbolicMetricFromEventFlow (ef : EventFlow) : Option HyperbolicMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicMetricUp.mk
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 0 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 1 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 2 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 3 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 4 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 5 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 6 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 7 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 8 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 9 ef))
      (hyperbolicMetricDecodeBHist (hyperbolicMetricEventAt 10 ef)))

private theorem hyperbolicMetric_round_trip (x : HyperbolicMetricUp) :
    hyperbolicMetricFromEventFlow (hyperbolicMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X d b t beta q F H C P N =>
      change
        some
          (HyperbolicMetricUp.mk
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist X))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist d))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist b))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist t))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist beta))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist q))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist F))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist H))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist C))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist P))
            (hyperbolicMetricDecodeBHist (hyperbolicMetricEncodeBHist N))) =
          some (HyperbolicMetricUp.mk X d b t beta q F H C P N)
      rw [hyperbolicMetric_decode_encode X, hyperbolicMetric_decode_encode d,
        hyperbolicMetric_decode_encode b, hyperbolicMetric_decode_encode t,
        hyperbolicMetric_decode_encode beta, hyperbolicMetric_decode_encode q,
        hyperbolicMetric_decode_encode F, hyperbolicMetric_decode_encode H,
        hyperbolicMetric_decode_encode C, hyperbolicMetric_decode_encode P,
        hyperbolicMetric_decode_encode N]

private theorem hyperbolicMetricToEventFlow_injective {x y : HyperbolicMetricUp} :
    hyperbolicMetricToEventFlow x = hyperbolicMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicMetricFromEventFlow (hyperbolicMetricToEventFlow x) =
        hyperbolicMetricFromEventFlow (hyperbolicMetricToEventFlow y) :=
    congrArg hyperbolicMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperbolicMetric_round_trip x).symm
      (Eq.trans hread (hyperbolicMetric_round_trip y)))

instance hyperbolicMetricBHistCarrier : BHistCarrier HyperbolicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicMetricToEventFlow
  fromEventFlow := hyperbolicMetricFromEventFlow

instance hyperbolicMetricChapterTasteGate : ChapterTasteGate HyperbolicMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperbolicMetricFromEventFlow (hyperbolicMetricToEventFlow x) = some x
    exact hyperbolicMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperbolicMetricToEventFlow_injective heq)

theorem HyperbolicMetricCarrier_namecert_obligations (M : HyperbolicMetricUp) :
    ∃ X d b t beta q F H C P N : BHist,
      hyperbolicMetricFields M = [X, d, b, t, beta, q, F, H, C, P, N] ∧
        hyperbolicMetricFromEventFlow
            (([X, d, b, t, beta, q, F, H, C, P, N] : List BHist).map
              hyperbolicMetricEncodeBHist) =
          some M ∧
          hyperbolicMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  cases M with
  | mk X d b t beta q F H C P N =>
      exact
        ⟨X, d, b, t, beta, q, F, H, C, P, N, rfl,
          hyperbolicMetric_round_trip (HyperbolicMetricUp.mk X d b t beta q F H C P N),
          rfl⟩

end BEDC.Derived.HyperbolicMetricUp
