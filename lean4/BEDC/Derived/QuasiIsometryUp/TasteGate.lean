import BEDC.Derived.QuasiIsometryUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuasiIsometryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def quasiIsometryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quasiIsometryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quasiIsometryEncodeBHist h

def quasiIsometryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quasiIsometryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quasiIsometryDecodeBHist tail)

private theorem QuasiIsometryTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, quasiIsometryDecodeBHist (quasiIsometryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quasiIsometryFields : QuasiIsometryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuasiIsometryUp.mk sourceMetric targetMetric coarseGraph distortion coarseSurjectivity
      distanceReadback completionFacing transport replay provenance name =>
      [sourceMetric, targetMetric, coarseGraph, distortion, coarseSurjectivity,
        distanceReadback, completionFacing, transport, replay, provenance, name]

def quasiIsometryToEventFlow : QuasiIsometryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (quasiIsometryFields x).map quasiIsometryEncodeBHist

private def quasiIsometryEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => quasiIsometryEventAt index rest

def quasiIsometryFromEventFlow : EventFlow → Option QuasiIsometryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (QuasiIsometryUp.mk
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 0 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 1 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 2 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 3 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 4 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 5 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 6 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 7 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 8 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 9 flow))
        (quasiIsometryDecodeBHist (quasiIsometryEventAt 10 flow)))

private theorem QuasiIsometryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : QuasiIsometryUp,
      quasiIsometryFromEventFlow (quasiIsometryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceMetric targetMetric coarseGraph distortion coarseSurjectivity distanceReadback
      completionFacing transport replay provenance name =>
      change
        some
          (QuasiIsometryUp.mk
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist sourceMetric))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist targetMetric))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist coarseGraph))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist distortion))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist coarseSurjectivity))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist distanceReadback))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist completionFacing))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist transport))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist replay))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist provenance))
            (quasiIsometryDecodeBHist (quasiIsometryEncodeBHist name))) =
          some
            (QuasiIsometryUp.mk sourceMetric targetMetric coarseGraph distortion
              coarseSurjectivity distanceReadback completionFacing transport replay provenance name)
      rw [QuasiIsometryTasteGate_single_carrier_alignment_decode_encode sourceMetric,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode targetMetric,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode coarseGraph,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode distortion,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode coarseSurjectivity,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode distanceReadback,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode completionFacing,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode transport,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode replay,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode provenance,
        QuasiIsometryTasteGate_single_carrier_alignment_decode_encode name]

private theorem QuasiIsometryToEventFlow_injective {x y : QuasiIsometryUp} :
    quasiIsometryToEventFlow x = quasiIsometryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quasiIsometryFromEventFlow (quasiIsometryToEventFlow x) =
        quasiIsometryFromEventFlow (quasiIsometryToEventFlow y) :=
    congrArg quasiIsometryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (QuasiIsometryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (QuasiIsometryTasteGate_single_carrier_alignment_round_trip y)))

instance quasiIsometryBHistCarrier : BHistCarrier QuasiIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quasiIsometryToEventFlow
  fromEventFlow := quasiIsometryFromEventFlow

instance quasiIsometryChapterTasteGate : ChapterTasteGate QuasiIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quasiIsometryFromEventFlow (quasiIsometryToEventFlow x) = some x
    exact QuasiIsometryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (QuasiIsometryToEventFlow_injective heq)

theorem QuasiIsometryTasteGate_single_carrier_alignment :
    (∀ h : BHist, quasiIsometryDecodeBHist (quasiIsometryEncodeBHist h) = h) ∧
      (∀ x : QuasiIsometryUp,
        quasiIsometryFromEventFlow (quasiIsometryToEventFlow x) = some x) ∧
        (∀ x y : QuasiIsometryUp,
          quasiIsometryToEventFlow x = quasiIsometryToEventFlow y → x = y) ∧
          quasiIsometryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨QuasiIsometryTasteGate_single_carrier_alignment_decode_encode,
      QuasiIsometryTasteGate_single_carrier_alignment_round_trip,
      fun _x _y heq => QuasiIsometryToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.QuasiIsometryUp
