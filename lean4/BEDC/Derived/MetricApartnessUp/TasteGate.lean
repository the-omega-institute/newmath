import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricApartnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricApartnessUp : Type where
  | packet
      (metric apartness distance witness transport replay provenance localName : BHist) :
      MetricApartnessUp
  deriving DecidableEq

def metricApartnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricApartnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricApartnessEncodeBHist h

def metricApartnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricApartnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricApartnessDecodeBHist tail)

private theorem metricApartness_decode_encode_bhist :
    ∀ h : BHist, metricApartnessDecodeBHist (metricApartnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metricApartnessFields : MetricApartnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricApartnessUp.packet metric apartness distance witness transport replay provenance
      localName =>
      [metric, apartness, distance, witness, transport, replay, provenance, localName]

def metricApartnessToEventFlow : MetricApartnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metricApartnessFields x).map metricApartnessEncodeBHist

private def metricApartnessEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => metricApartnessEventAt index rest

def metricApartnessFromEventFlow (ef : EventFlow) : Option MetricApartnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetricApartnessUp.packet
      (metricApartnessDecodeBHist (metricApartnessEventAt 0 ef))
      (metricApartnessDecodeBHist (metricApartnessEventAt 1 ef))
      (metricApartnessDecodeBHist (metricApartnessEventAt 2 ef))
      (metricApartnessDecodeBHist (metricApartnessEventAt 3 ef))
      (metricApartnessDecodeBHist (metricApartnessEventAt 4 ef))
      (metricApartnessDecodeBHist (metricApartnessEventAt 5 ef))
      (metricApartnessDecodeBHist (metricApartnessEventAt 6 ef))
      (metricApartnessDecodeBHist (metricApartnessEventAt 7 ef)))

private theorem metricApartness_round_trip (x : MetricApartnessUp) :
    metricApartnessFromEventFlow (metricApartnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet metric apartness distance witness transport replay provenance localName =>
      change
        some
          (MetricApartnessUp.packet
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist metric))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist apartness))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist distance))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist witness))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist transport))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist replay))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist provenance))
            (metricApartnessDecodeBHist (metricApartnessEncodeBHist localName))) =
          some
            (MetricApartnessUp.packet metric apartness distance witness transport replay
              provenance localName)
      rw [metricApartness_decode_encode_bhist metric,
        metricApartness_decode_encode_bhist apartness,
        metricApartness_decode_encode_bhist distance,
        metricApartness_decode_encode_bhist witness,
        metricApartness_decode_encode_bhist transport,
        metricApartness_decode_encode_bhist replay,
        metricApartness_decode_encode_bhist provenance,
        metricApartness_decode_encode_bhist localName]

private theorem metricApartnessToEventFlow_injective {x y : MetricApartnessUp} :
    metricApartnessToEventFlow x = metricApartnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricApartnessFromEventFlow (metricApartnessToEventFlow x) =
        metricApartnessFromEventFlow (metricApartnessToEventFlow y) :=
    congrArg metricApartnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricApartness_round_trip x).symm
      (Eq.trans hread (metricApartness_round_trip y)))

instance MetricApartnessTasteGate_single_carrier_alignment :
    BHistCarrier MetricApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricApartnessToEventFlow
  fromEventFlow := metricApartnessFromEventFlow

instance metricApartnessChapterTasteGate : ChapterTasteGate MetricApartnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricApartnessFromEventFlow (metricApartnessToEventFlow x) = some x
    exact metricApartness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricApartnessToEventFlow_injective heq)

end BEDC.Derived.MetricApartnessUp
