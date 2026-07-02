import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorStieltjesMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorStieltjesMeasureUp : Type where
  | mk (F I L W R S H C P N : BHist) : CantorStieltjesMeasureUp
  deriving DecidableEq

def cantorStieltjesMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorStieltjesMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorStieltjesMeasureEncodeBHist h

def cantorStieltjesMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorStieltjesMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorStieltjesMeasureDecodeBHist tail)

private theorem CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorStieltjesMeasureToEventFlow : CantorStieltjesMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CantorStieltjesMeasureUp.mk F I L W R S H C P N =>
      [cantorStieltjesMeasureEncodeBHist F,
        cantorStieltjesMeasureEncodeBHist I,
        cantorStieltjesMeasureEncodeBHist L,
        cantorStieltjesMeasureEncodeBHist W,
        cantorStieltjesMeasureEncodeBHist R,
        cantorStieltjesMeasureEncodeBHist S,
        cantorStieltjesMeasureEncodeBHist H,
        cantorStieltjesMeasureEncodeBHist C,
        cantorStieltjesMeasureEncodeBHist P,
        cantorStieltjesMeasureEncodeBHist N]

private def cantorStieltjesMeasureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorStieltjesMeasureEventAtDefault index rest

def cantorStieltjesMeasureFromEventFlow : EventFlow → Option CantorStieltjesMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CantorStieltjesMeasureUp.mk
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 0 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 1 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 2 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 3 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 4 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 5 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 6 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 7 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 8 ef))
        (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEventAtDefault 9 ef)))

private theorem CantorStieltjesMeasureTasteGate_single_carrier_alignment_round_trip
    (x : CantorStieltjesMeasureUp) :
    cantorStieltjesMeasureFromEventFlow (cantorStieltjesMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F I L W R S H C P N =>
      change
        some
          (CantorStieltjesMeasureUp.mk
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist F))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist I))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist L))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist W))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist R))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist S))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist H))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist C))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist P))
            (cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist N))) =
          some (CantorStieltjesMeasureUp.mk F I L W R S H C P N)
      rw [CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode F,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode I,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode L,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode W,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode R,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode S,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode H,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode C,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode P,
        CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode N]

private theorem CantorStieltjesMeasureTasteGate_single_carrier_alignment_injective
    {x y : CantorStieltjesMeasureUp} :
    cantorStieltjesMeasureToEventFlow x = cantorStieltjesMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorStieltjesMeasureFromEventFlow (cantorStieltjesMeasureToEventFlow x) =
        cantorStieltjesMeasureFromEventFlow (cantorStieltjesMeasureToEventFlow y) :=
    congrArg cantorStieltjesMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CantorStieltjesMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CantorStieltjesMeasureTasteGate_single_carrier_alignment_round_trip y)))

instance cantorStieltjesMeasureBHistCarrier : BHistCarrier CantorStieltjesMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorStieltjesMeasureToEventFlow
  fromEventFlow := cantorStieltjesMeasureFromEventFlow

instance cantorStieltjesMeasureChapterTasteGate :
    ChapterTasteGate CantorStieltjesMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorStieltjesMeasureFromEventFlow (cantorStieltjesMeasureToEventFlow x) =
      some x
    exact CantorStieltjesMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorStieltjesMeasureTasteGate_single_carrier_alignment_injective heq)

theorem CantorStieltjesMeasureTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        cantorStieltjesMeasureDecodeBHist (cantorStieltjesMeasureEncodeBHist h) = h) ∧
      (∀ x : CantorStieltjesMeasureUp,
        cantorStieltjesMeasureFromEventFlow (cantorStieltjesMeasureToEventFlow x) = some x) ∧
      (∀ x y : CantorStieltjesMeasureUp,
        cantorStieltjesMeasureToEventFlow x = cantorStieltjesMeasureToEventFlow y → x = y) ∧
      Nonempty (ChapterTasteGate CantorStieltjesMeasureUp) ∧
      cantorStieltjesMeasureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  have roundTrip :
      ∀ x : CantorStieltjesMeasureUp,
        cantorStieltjesMeasureFromEventFlow (cantorStieltjesMeasureToEventFlow x) = some x :=
    CantorStieltjesMeasureTasteGate_single_carrier_alignment_round_trip
  have injective :
      ∀ x y : CantorStieltjesMeasureUp,
        cantorStieltjesMeasureToEventFlow x = cantorStieltjesMeasureToEventFlow y → x = y := by
    intro x y heq
    exact CantorStieltjesMeasureTasteGate_single_carrier_alignment_injective heq
  exact
    ⟨CantorStieltjesMeasureTasteGate_single_carrier_alignment_decode_encode,
      roundTrip,
      injective,
      ⟨cantorStieltjesMeasureChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CantorStieltjesMeasureUp
