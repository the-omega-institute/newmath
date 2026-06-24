import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.YoungMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive YoungMeasureUp : Type where
  | mk (R P T S Q E H C K N : BHist) : YoungMeasureUp
  deriving DecidableEq

def youngMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: youngMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: youngMeasureEncodeBHist h

def youngMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (youngMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (youngMeasureDecodeBHist tail)

private theorem YoungMeasureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, youngMeasureDecodeBHist (youngMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def youngMeasureFields : YoungMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | YoungMeasureUp.mk R P T S Q E H C K N => [R, P, T, S, Q, E, H, C, K, N]

def youngMeasureToEventFlow : YoungMeasureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (youngMeasureFields x).map youngMeasureEncodeBHist

private def youngMeasureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => youngMeasureEventAtDefault index rest

def youngMeasureFromEventFlow (ef : EventFlow) : Option YoungMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (YoungMeasureUp.mk
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 0 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 1 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 2 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 3 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 4 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 5 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 6 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 7 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 8 ef))
      (youngMeasureDecodeBHist (youngMeasureEventAtDefault 9 ef)))

private theorem YoungMeasureTasteGate_single_carrier_alignment_round_trip
    (x : YoungMeasureUp) :
    youngMeasureFromEventFlow (youngMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R P T S Q E H C K N =>
      change
        some
          (YoungMeasureUp.mk
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist R))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist P))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist T))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist S))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist Q))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist E))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist H))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist C))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist K))
            (youngMeasureDecodeBHist (youngMeasureEncodeBHist N))) =
          some (YoungMeasureUp.mk R P T S Q E H C K N)
      rw [YoungMeasureTasteGate_single_carrier_alignment_decode_encode R,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode P,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode T,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode S,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode Q,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode E,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode H,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode C,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode K,
        YoungMeasureTasteGate_single_carrier_alignment_decode_encode N]

private theorem YoungMeasureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : YoungMeasureUp} :
    youngMeasureToEventFlow x = youngMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      youngMeasureFromEventFlow (youngMeasureToEventFlow x) =
        youngMeasureFromEventFlow (youngMeasureToEventFlow y) :=
    congrArg youngMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (YoungMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (YoungMeasureTasteGate_single_carrier_alignment_round_trip y)))

instance youngMeasureBHistCarrier : BHistCarrier YoungMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := youngMeasureToEventFlow
  fromEventFlow := youngMeasureFromEventFlow

instance youngMeasureChapterTasteGate : ChapterTasteGate YoungMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change youngMeasureFromEventFlow (youngMeasureToEventFlow x) = some x
    exact YoungMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (YoungMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate YoungMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  youngMeasureChapterTasteGate

theorem YoungMeasureTasteGate_single_carrier_alignment :
    (∀ h : BHist, youngMeasureDecodeBHist (youngMeasureEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier YoungMeasureUp) ∧
        Nonempty (ChapterTasteGate YoungMeasureUp) ∧
          youngMeasureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨YoungMeasureTasteGate_single_carrier_alignment_decode_encode,
      ⟨youngMeasureBHistCarrier⟩,
      ⟨youngMeasureChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.YoungMeasureUp
