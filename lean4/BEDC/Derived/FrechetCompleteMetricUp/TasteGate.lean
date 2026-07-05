import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetCompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetCompleteMetricUp : Type where
  | mk (M S R D T E H C P N : BHist) : FrechetCompleteMetricUp
  deriving DecidableEq

def frechetCompleteMetricEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetCompleteMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetCompleteMetricEncodeBHist h

def frechetCompleteMetricDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetCompleteMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetCompleteMetricDecodeBHist tail)

private theorem FrechetCompleteMetricTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frechetCompleteMetricFields : FrechetCompleteMetricUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetCompleteMetricUp.mk M S R D T E H C P N => [M, S, R, D, T, E, H, C, P, N]

def frechetCompleteMetricToEventFlow : FrechetCompleteMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (frechetCompleteMetricFields x).map frechetCompleteMetricEncodeBHist

private def frechetCompleteMetricEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frechetCompleteMetricEventAtDefault index rest

def frechetCompleteMetricFromEventFlow (ef : EventFlow) : Option FrechetCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FrechetCompleteMetricUp.mk
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 0 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 1 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 2 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 3 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 4 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 5 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 6 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 7 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 8 ef))
      (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEventAtDefault 9 ef)))

private theorem FrechetCompleteMetricTasteGate_single_carrier_alignment_round_trip :
    forall x : FrechetCompleteMetricUp,
      frechetCompleteMetricFromEventFlow (frechetCompleteMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S R D T E H C P N =>
      change
        some
            (FrechetCompleteMetricUp.mk
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist M))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist S))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist R))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist D))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist T))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist E))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist H))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist C))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist P))
              (frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist N))) =
          some (FrechetCompleteMetricUp.mk M S R D T E H C P N)
      rw [FrechetCompleteMetricTasteGate_single_carrier_alignment_decode M,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode S,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode R,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode D,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode T,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode E,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode H,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode C,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode P,
        FrechetCompleteMetricTasteGate_single_carrier_alignment_decode N]

private theorem FrechetCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrechetCompleteMetricUp} :
    frechetCompleteMetricToEventFlow x = frechetCompleteMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetCompleteMetricFromEventFlow (frechetCompleteMetricToEventFlow x) =
        frechetCompleteMetricFromEventFlow (frechetCompleteMetricToEventFlow y) :=
    congrArg frechetCompleteMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrechetCompleteMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FrechetCompleteMetricTasteGate_single_carrier_alignment_round_trip y)))

instance frechetCompleteMetricBHistCarrier : BHistCarrier FrechetCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetCompleteMetricToEventFlow
  fromEventFlow := frechetCompleteMetricFromEventFlow

instance frechetCompleteMetricChapterTasteGate : ChapterTasteGate FrechetCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetCompleteMetricFromEventFlow (frechetCompleteMetricToEventFlow x) = some x
    exact FrechetCompleteMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrechetCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FrechetCompleteMetricTasteGate_single_carrier_alignment :
    (forall h : BHist,
      frechetCompleteMetricDecodeBHist (frechetCompleteMetricEncodeBHist h) = h) ∧
      (forall x : FrechetCompleteMetricUp,
        frechetCompleteMetricFromEventFlow (frechetCompleteMetricToEventFlow x) = some x) ∧
        (forall x y : FrechetCompleteMetricUp,
          frechetCompleteMetricToEventFlow x = frechetCompleteMetricToEventFlow y -> x = y) ∧
          frechetCompleteMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FrechetCompleteMetricTasteGate_single_carrier_alignment_decode,
      ⟨FrechetCompleteMetricTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
          FrechetCompleteMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.FrechetCompleteMetricUp
