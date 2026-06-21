import BEDC.Derived.RealCauchyRateUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCauchyRateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realCauchyRateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCauchyRateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCauchyRateEncodeBHist h

def realCauchyRateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCauchyRateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCauchyRateDecodeBHist tail)

private theorem realCauchyRateDecode_encode :
    ∀ h : BHist, realCauchyRateDecodeBHist (realCauchyRateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCauchyRateToEventFlow : RealCauchyRateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realCauchyRateFields x).map realCauchyRateEncodeBHist

private def realCauchyRateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realCauchyRateEventAtDefault index rest

def realCauchyRateFromEventFlow : EventFlow → Option RealCauchyRateUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (RealCauchyRateUp.mk
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 0 ef))
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 1 ef))
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 2 ef))
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 3 ef))
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 4 ef))
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 5 ef))
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 6 ef))
          (realCauchyRateDecodeBHist (realCauchyRateEventAtDefault 7 ef)))

private theorem realCauchyRate_round_trip :
    ∀ x : RealCauchyRateUp,
      realCauchyRateFromEventFlow (realCauchyRateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S Q R H C P N =>
      change
        some
          (RealCauchyRateUp.mk
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist D))
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist S))
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist Q))
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist R))
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist H))
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist C))
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist P))
            (realCauchyRateDecodeBHist (realCauchyRateEncodeBHist N))) =
          some (RealCauchyRateUp.mk D S Q R H C P N)
      rw [realCauchyRateDecode_encode D, realCauchyRateDecode_encode S,
        realCauchyRateDecode_encode Q, realCauchyRateDecode_encode R,
        realCauchyRateDecode_encode H, realCauchyRateDecode_encode C,
        realCauchyRateDecode_encode P, realCauchyRateDecode_encode N]

private theorem realCauchyRateToEventFlow_injective {x y : RealCauchyRateUp} :
    realCauchyRateToEventFlow x = realCauchyRateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCauchyRateFromEventFlow (realCauchyRateToEventFlow x) =
        realCauchyRateFromEventFlow (realCauchyRateToEventFlow y) :=
    congrArg realCauchyRateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCauchyRate_round_trip x).symm
      (Eq.trans hread (realCauchyRate_round_trip y)))

instance realCauchyRateBHistCarrier : BHistCarrier RealCauchyRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCauchyRateToEventFlow
  fromEventFlow := realCauchyRateFromEventFlow

instance realCauchyRateChapterTasteGate : ChapterTasteGate RealCauchyRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realCauchyRateFromEventFlow (realCauchyRateToEventFlow x) = some x
    exact realCauchyRate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCauchyRateToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCauchyRateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCauchyRateChapterTasteGate

theorem RealCauchyRateTasteGate_single_carrier_alignment :
    (∀ h : BHist, realCauchyRateDecodeBHist (realCauchyRateEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BEDC.Derived.RealCauchyRateUp) ∧
        Nonempty (ChapterTasteGate BEDC.Derived.RealCauchyRateUp) ∧
          realCauchyRateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨realCauchyRateDecode_encode, ⟨realCauchyRateBHistCarrier⟩,
      ⟨realCauchyRateChapterTasteGate⟩, rfl⟩

end BEDC.Derived.RealCauchyRateUp
