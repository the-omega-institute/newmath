import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntervalHalvingModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntervalHalvingModulusUp : Type where
  | mk (I L S R D E H C P N : BHist) : IntervalHalvingModulusUp
  deriving DecidableEq

def intervalHalvingModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: intervalHalvingModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: intervalHalvingModulusEncodeBHist h

def intervalHalvingModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (intervalHalvingModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (intervalHalvingModulusDecodeBHist tail)

private theorem IntervalHalvingModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def intervalHalvingModulusFields : IntervalHalvingModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntervalHalvingModulusUp.mk I L S R D E H C P N =>
      [I, L, S, R, D, E, H, C, P, N]

def intervalHalvingModulusToEventFlow : IntervalHalvingModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (intervalHalvingModulusFields x).map intervalHalvingModulusEncodeBHist

private def IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt index rest

def intervalHalvingModulusFromEventFlow (ef : EventFlow) : Option IntervalHalvingModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (IntervalHalvingModulusUp.mk
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 0 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 1 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 2 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 3 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 4 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 5 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 6 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 7 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 8 ef))
      (intervalHalvingModulusDecodeBHist
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem IntervalHalvingModulusTasteGate_single_carrier_alignment_round_trip
    (x : IntervalHalvingModulusUp) :
    intervalHalvingModulusFromEventFlow (intervalHalvingModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I L S R D E H C P N =>
      change
        some
            (IntervalHalvingModulusUp.mk
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist I))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist L))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist S))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist R))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist D))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist E))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist H))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist C))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist P))
              (intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist N))) =
          some (IntervalHalvingModulusUp.mk I L S R D E H C P N)
      rw [IntervalHalvingModulusTasteGate_single_carrier_alignment_decode I,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode L,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode S,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode R,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode D,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode E,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode H,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode C,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode P,
        IntervalHalvingModulusTasteGate_single_carrier_alignment_decode N]

private theorem IntervalHalvingModulusTasteGate_single_carrier_alignment_injective
    {x y : IntervalHalvingModulusUp} :
    intervalHalvingModulusToEventFlow x = intervalHalvingModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      intervalHalvingModulusFromEventFlow (intervalHalvingModulusToEventFlow x) =
        intervalHalvingModulusFromEventFlow (intervalHalvingModulusToEventFlow y) :=
    congrArg intervalHalvingModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (IntervalHalvingModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (IntervalHalvingModulusTasteGate_single_carrier_alignment_round_trip y)))

instance intervalHalvingModulusBHistCarrier :
    BHistCarrier IntervalHalvingModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := intervalHalvingModulusToEventFlow
  fromEventFlow := intervalHalvingModulusFromEventFlow

instance intervalHalvingModulusChapterTasteGate :
    ChapterTasteGate IntervalHalvingModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      intervalHalvingModulusFromEventFlow (intervalHalvingModulusToEventFlow x) =
        some x
    exact IntervalHalvingModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntervalHalvingModulusTasteGate_single_carrier_alignment_injective heq)

theorem IntervalHalvingModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      intervalHalvingModulusDecodeBHist (intervalHalvingModulusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier IntervalHalvingModulusUp) ∧
        Nonempty (ChapterTasteGate IntervalHalvingModulusUp) ∧
          intervalHalvingModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨IntervalHalvingModulusTasteGate_single_carrier_alignment_decode,
      ⟨intervalHalvingModulusBHistCarrier⟩,
      ⟨intervalHalvingModulusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.IntervalHalvingModulusUp.TasteGate
