import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VariationMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VariationMeasureUp : Type where
  | mk (B J Pi E X D V A R H C P N : BHist) : VariationMeasureUp
  deriving DecidableEq

def variationMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: variationMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: variationMeasureEncodeBHist h

def variationMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (variationMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (variationMeasureDecodeBHist tail)

private theorem VariationMeasureTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, variationMeasureDecodeBHist (variationMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def variationMeasureFields : VariationMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VariationMeasureUp.mk B J Pi E X D V A R H C P N =>
      [B, J, Pi, E, X, D, V, A, R, H, C, P, N]

def variationMeasureToEventFlow : VariationMeasureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (variationMeasureFields x).map variationMeasureEncodeBHist

private def VariationMeasureTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      VariationMeasureTasteGate_single_carrier_alignment_eventAt index rest

def variationMeasureFromEventFlow (ef : EventFlow) : Option VariationMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (VariationMeasureUp.mk
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 0 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 1 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 2 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 3 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 4 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 5 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 6 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 7 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 8 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 9 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 10 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 11 ef))
      (variationMeasureDecodeBHist
        (VariationMeasureTasteGate_single_carrier_alignment_eventAt 12 ef)))

private theorem VariationMeasureTasteGate_single_carrier_alignment_round_trip
    (x : VariationMeasureUp) :
    variationMeasureFromEventFlow (variationMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B J Pi E X D V A R H C P N =>
      change
        some
          (VariationMeasureUp.mk
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist B))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist J))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist Pi))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist E))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist X))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist D))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist V))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist A))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist R))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist H))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist C))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist P))
            (variationMeasureDecodeBHist (variationMeasureEncodeBHist N))) =
          some (VariationMeasureUp.mk B J Pi E X D V A R H C P N)
      rw [VariationMeasureTasteGate_single_carrier_alignment_decode B,
        VariationMeasureTasteGate_single_carrier_alignment_decode J,
        VariationMeasureTasteGate_single_carrier_alignment_decode Pi,
        VariationMeasureTasteGate_single_carrier_alignment_decode E,
        VariationMeasureTasteGate_single_carrier_alignment_decode X,
        VariationMeasureTasteGate_single_carrier_alignment_decode D,
        VariationMeasureTasteGate_single_carrier_alignment_decode V,
        VariationMeasureTasteGate_single_carrier_alignment_decode A,
        VariationMeasureTasteGate_single_carrier_alignment_decode R,
        VariationMeasureTasteGate_single_carrier_alignment_decode H,
        VariationMeasureTasteGate_single_carrier_alignment_decode C,
        VariationMeasureTasteGate_single_carrier_alignment_decode P,
        VariationMeasureTasteGate_single_carrier_alignment_decode N]

private theorem VariationMeasureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : VariationMeasureUp} :
    variationMeasureToEventFlow x = variationMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      variationMeasureFromEventFlow (variationMeasureToEventFlow x) =
        variationMeasureFromEventFlow (variationMeasureToEventFlow y) :=
    congrArg variationMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (VariationMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (VariationMeasureTasteGate_single_carrier_alignment_round_trip y)))

instance variationMeasureBHistCarrier : BHistCarrier VariationMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := variationMeasureToEventFlow
  fromEventFlow := variationMeasureFromEventFlow

instance variationMeasureChapterTasteGate : ChapterTasteGate VariationMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change variationMeasureFromEventFlow (variationMeasureToEventFlow x) = some x
    exact VariationMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (VariationMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate VariationMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  variationMeasureChapterTasteGate

theorem VariationMeasureTasteGate_single_carrier_alignment :
    (forall h : BHist, variationMeasureDecodeBHist (variationMeasureEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier VariationMeasureUp) ∧
        Nonempty (ChapterTasteGate VariationMeasureUp) ∧
          variationMeasureEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨VariationMeasureTasteGate_single_carrier_alignment_decode,
      ⟨variationMeasureBHistCarrier⟩,
      ⟨variationMeasureChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.VariationMeasureUp
