import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NeumannSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NeumannSeriesUp : Type where
  | mk (A T K W S Q R E H C P L : BHist) : NeumannSeriesUp
  deriving DecidableEq

def neumannSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: neumannSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: neumannSeriesEncodeBHist h

def neumannSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (neumannSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (neumannSeriesDecodeBHist tail)

private theorem NeumannSeriesTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, neumannSeriesDecodeBHist (neumannSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def neumannSeriesToEventFlow : NeumannSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NeumannSeriesUp.mk A T K W S Q R E H C P L =>
      [neumannSeriesEncodeBHist A,
        neumannSeriesEncodeBHist T,
        neumannSeriesEncodeBHist K,
        neumannSeriesEncodeBHist W,
        neumannSeriesEncodeBHist S,
        neumannSeriesEncodeBHist Q,
        neumannSeriesEncodeBHist R,
        neumannSeriesEncodeBHist E,
        neumannSeriesEncodeBHist H,
        neumannSeriesEncodeBHist C,
        neumannSeriesEncodeBHist P,
        neumannSeriesEncodeBHist L]

def neumannSeriesFromEventFlow : EventFlow → Option NeumannSeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | A :: T :: K :: W :: S :: Q :: R :: E :: H :: C :: P :: L :: [] =>
      some
        (NeumannSeriesUp.mk
          (neumannSeriesDecodeBHist A)
          (neumannSeriesDecodeBHist T)
          (neumannSeriesDecodeBHist K)
          (neumannSeriesDecodeBHist W)
          (neumannSeriesDecodeBHist S)
          (neumannSeriesDecodeBHist Q)
          (neumannSeriesDecodeBHist R)
          (neumannSeriesDecodeBHist E)
          (neumannSeriesDecodeBHist H)
          (neumannSeriesDecodeBHist C)
          (neumannSeriesDecodeBHist P)
          (neumannSeriesDecodeBHist L))
  | _ => none

private theorem NeumannSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NeumannSeriesUp,
      neumannSeriesFromEventFlow (neumannSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A T K W S Q R E H C P L =>
      change
        some
          (NeumannSeriesUp.mk
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist A))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist T))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist K))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist W))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist S))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist Q))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist R))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist E))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist H))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist C))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist P))
            (neumannSeriesDecodeBHist (neumannSeriesEncodeBHist L))) =
          some (NeumannSeriesUp.mk A T K W S Q R E H C P L)
      rw [NeumannSeriesTasteGate_single_carrier_alignment_decode A,
        NeumannSeriesTasteGate_single_carrier_alignment_decode T,
        NeumannSeriesTasteGate_single_carrier_alignment_decode K,
        NeumannSeriesTasteGate_single_carrier_alignment_decode W,
        NeumannSeriesTasteGate_single_carrier_alignment_decode S,
        NeumannSeriesTasteGate_single_carrier_alignment_decode Q,
        NeumannSeriesTasteGate_single_carrier_alignment_decode R,
        NeumannSeriesTasteGate_single_carrier_alignment_decode E,
        NeumannSeriesTasteGate_single_carrier_alignment_decode H,
        NeumannSeriesTasteGate_single_carrier_alignment_decode C,
        NeumannSeriesTasteGate_single_carrier_alignment_decode P,
        NeumannSeriesTasteGate_single_carrier_alignment_decode L]

private theorem NeumannSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NeumannSeriesUp} :
    neumannSeriesToEventFlow x = neumannSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      neumannSeriesFromEventFlow (neumannSeriesToEventFlow x) =
        neumannSeriesFromEventFlow (neumannSeriesToEventFlow y) :=
    congrArg neumannSeriesFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans
      (NeumannSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NeumannSeriesTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance neumannSeriesBHistCarrier : BHistCarrier NeumannSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := neumannSeriesToEventFlow
  fromEventFlow := neumannSeriesFromEventFlow

instance neumannSeriesChapterTasteGate : ChapterTasteGate NeumannSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change neumannSeriesFromEventFlow (neumannSeriesToEventFlow x) = some x
    exact NeumannSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NeumannSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate NeumannSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  neumannSeriesChapterTasteGate

end BEDC.Derived.NeumannSeriesUp
