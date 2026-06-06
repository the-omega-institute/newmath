import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalConnectednessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalConnectednessUp : Type where
  | mk (E L D S R T C P N : BHist) : IntervalConnectednessUp
  deriving DecidableEq

def intervalConnectednessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalConnectednessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalConnectednessEncodeBHist h

def intervalConnectednessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalConnectednessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalConnectednessDecodeBHist tail)

private theorem IntervalConnectednessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, intervalConnectednessDecodeBHist
      (intervalConnectednessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def IntervalConnectednessTasteGate_single_carrier_alignment_fields :
    IntervalConnectednessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalConnectednessUp.mk E L D S R T C P N => [E, L, D, S, R, T, C, P, N]

def IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow :
    IntervalConnectednessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (IntervalConnectednessTasteGate_single_carrier_alignment_fields x).map
        intervalConnectednessEncodeBHist

private def IntervalConnectednessTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      IntervalConnectednessTasteGate_single_carrier_alignment_eventAt index rest

def IntervalConnectednessTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option IntervalConnectednessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalConnectednessUp.mk
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 0 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 1 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 2 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 3 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 4 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 5 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 6 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 7 ef))
      (intervalConnectednessDecodeBHist
        (IntervalConnectednessTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem IntervalConnectednessTasteGate_single_carrier_alignment_round_trip
    (x : IntervalConnectednessUp) :
    IntervalConnectednessTasteGate_single_carrier_alignment_fromEventFlow
      (IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E L D S R T C P N =>
      change
        some
          (IntervalConnectednessUp.mk
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist E))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist L))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist D))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist S))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist R))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist T))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist C))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist P))
            (intervalConnectednessDecodeBHist (intervalConnectednessEncodeBHist N))) =
          some (IntervalConnectednessUp.mk E L D S R T C P N)
      rw [IntervalConnectednessTasteGate_single_carrier_alignment_decode E,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode L,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode D,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode S,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode R,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode T,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode C,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode P,
        IntervalConnectednessTasteGate_single_carrier_alignment_decode N]

private theorem IntervalConnectednessTasteGate_single_carrier_alignment_injective
    {x y : IntervalConnectednessUp} :
    IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow x =
      IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      IntervalConnectednessTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow x) =
        IntervalConnectednessTasteGate_single_carrier_alignment_fromEventFlow
          (IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg IntervalConnectednessTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IntervalConnectednessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntervalConnectednessTasteGate_single_carrier_alignment_round_trip y)))

instance IntervalConnectednessTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier IntervalConnectednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := IntervalConnectednessTasteGate_single_carrier_alignment_fromEventFlow

instance IntervalConnectednessTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate IntervalConnectednessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      IntervalConnectednessTasteGate_single_carrier_alignment_fromEventFlow
        (IntervalConnectednessTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact IntervalConnectednessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalConnectednessTasteGate_single_carrier_alignment_injective heq)

theorem IntervalConnectednessTasteGate_single_carrier_alignment :
    (forall h : BHist, intervalConnectednessDecodeBHist
      (intervalConnectednessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier IntervalConnectednessUp) ∧
        Nonempty (ChapterTasteGate IntervalConnectednessUp) ∧
          intervalConnectednessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨IntervalConnectednessTasteGate_single_carrier_alignment_decode,
      ⟨IntervalConnectednessTasteGate_single_carrier_alignment_BHistCarrier⟩,
      ⟨IntervalConnectednessTasteGate_single_carrier_alignment_ChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.IntervalConnectednessUp
