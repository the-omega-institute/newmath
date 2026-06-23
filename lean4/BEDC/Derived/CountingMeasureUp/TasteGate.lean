import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CountingMeasureUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CountingMeasureUp : Type where
  | mk (E F T L R H C P N : BHist) : CountingMeasureUp
  deriving DecidableEq

def countingMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: countingMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: countingMeasureEncodeBHist h

def countingMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (countingMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (countingMeasureDecodeBHist tail)

private theorem CountingMeasureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, countingMeasureDecodeBHist (countingMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def countingMeasureToEventFlow : CountingMeasureUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CountingMeasureUp.mk E F T L R H C P N =>
      [countingMeasureEncodeBHist E,
        countingMeasureEncodeBHist F,
        countingMeasureEncodeBHist T,
        countingMeasureEncodeBHist L,
        countingMeasureEncodeBHist R,
        countingMeasureEncodeBHist H,
        countingMeasureEncodeBHist C,
        countingMeasureEncodeBHist P,
        countingMeasureEncodeBHist N]

private def countingMeasureEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => countingMeasureEventAtDefault index rest

def countingMeasureFromEventFlow (ef : EventFlow) : Option CountingMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CountingMeasureUp.mk
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 0 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 1 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 2 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 3 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 4 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 5 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 6 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 7 ef))
      (countingMeasureDecodeBHist (countingMeasureEventAtDefault 8 ef)))

private theorem CountingMeasureTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CountingMeasureUp,
      countingMeasureFromEventFlow (countingMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E F T L R H C P N =>
      change
        some
            (CountingMeasureUp.mk
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist E))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist F))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist T))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist L))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist R))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist H))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist C))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist P))
              (countingMeasureDecodeBHist (countingMeasureEncodeBHist N))) =
          some (CountingMeasureUp.mk E F T L R H C P N)
      rw [CountingMeasureTasteGate_single_carrier_alignment_decode E,
        CountingMeasureTasteGate_single_carrier_alignment_decode F,
        CountingMeasureTasteGate_single_carrier_alignment_decode T,
        CountingMeasureTasteGate_single_carrier_alignment_decode L,
        CountingMeasureTasteGate_single_carrier_alignment_decode R,
        CountingMeasureTasteGate_single_carrier_alignment_decode H,
        CountingMeasureTasteGate_single_carrier_alignment_decode C,
        CountingMeasureTasteGate_single_carrier_alignment_decode P,
        CountingMeasureTasteGate_single_carrier_alignment_decode N]

private theorem CountingMeasureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CountingMeasureUp} :
    countingMeasureToEventFlow x = countingMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      countingMeasureFromEventFlow (countingMeasureToEventFlow x) =
        countingMeasureFromEventFlow (countingMeasureToEventFlow y) :=
    congrArg countingMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CountingMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CountingMeasureTasteGate_single_carrier_alignment_round_trip y)))

private def countingMeasureFields : CountingMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CountingMeasureUp.mk E F T L R H C P N => [E, F, T, L, R, H, C, P, N]

private theorem CountingMeasureTasteGate_single_carrier_alignment_fields :
    ∀ x y : CountingMeasureUp, countingMeasureFields x = countingMeasureFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E1 F1 T1 L1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk E2 F2 T2 L2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance countingMeasureBHistCarrier : BHistCarrier CountingMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := countingMeasureToEventFlow
  fromEventFlow := countingMeasureFromEventFlow

instance countingMeasureChapterTasteGate : ChapterTasteGate CountingMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change countingMeasureFromEventFlow (countingMeasureToEventFlow x) = some x
    exact CountingMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CountingMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance countingMeasureFieldFaithful : FieldFaithful CountingMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := countingMeasureFields
  field_faithful := CountingMeasureTasteGate_single_carrier_alignment_fields

instance countingMeasureNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CountingMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CountingMeasureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CountingMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CountingMeasureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CountingMeasureUp) ∧
      Nonempty (FieldFaithful CountingMeasureUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CountingMeasureUp) ∧
          countingMeasureEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ h : BHist, countingMeasureDecodeBHist (countingMeasureEncodeBHist h) = h) ∧
              (∀ x : CountingMeasureUp,
                countingMeasureFromEventFlow (countingMeasureToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨countingMeasureChapterTasteGate⟩,
      ⟨countingMeasureFieldFaithful⟩,
      ⟨countingMeasureNontrivial⟩,
      rfl,
      CountingMeasureTasteGate_single_carrier_alignment_decode,
      CountingMeasureTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.CountingMeasureUp.TasteGate
