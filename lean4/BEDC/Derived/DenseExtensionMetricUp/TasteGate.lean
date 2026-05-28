import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DenseExtensionMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DenseExtensionMetricUp : Type where
  | mk (X J omega M Y S R D Q T H C P N : BHist) : DenseExtensionMetricUp
  deriving DecidableEq

def denseExtensionMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: denseExtensionMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: denseExtensionMetricEncodeBHist h

def denseExtensionMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (denseExtensionMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (denseExtensionMetricDecodeBHist tail)

private theorem DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def denseExtensionMetricFields : DenseExtensionMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DenseExtensionMetricUp.mk X J omega M Y S R D Q T H C P N =>
      [X, J, omega, M, Y, S, R, D, Q, T, H, C, P, N]

def denseExtensionMetricToEventFlow : DenseExtensionMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (denseExtensionMetricFields x).map denseExtensionMetricEncodeBHist

private def denseExtensionMetricEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => denseExtensionMetricEventAt index rest

def denseExtensionMetricFromEventFlow (ef : EventFlow) : Option DenseExtensionMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DenseExtensionMetricUp.mk
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 0 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 1 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 2 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 3 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 4 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 5 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 6 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 7 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 8 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 9 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 10 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 11 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 12 ef))
      (denseExtensionMetricDecodeBHist (denseExtensionMetricEventAt 13 ef)))

private theorem DenseExtensionMetricTasteGate_single_carrier_alignment_round_trip
    (x : DenseExtensionMetricUp) :
    denseExtensionMetricFromEventFlow (denseExtensionMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X J omega M Y S R D Q T H C P N =>
      change
        some
          (DenseExtensionMetricUp.mk
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist X))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist J))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist omega))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist M))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist Y))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist S))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist R))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist D))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist Q))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist T))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist H))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist C))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist P))
            (denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist N))) =
          some (DenseExtensionMetricUp.mk X J omega M Y S R D Q T H C P N)
      rw [DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode X,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode J,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode omega,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode M,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode Y,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode S,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode R,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode D,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode Q,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode T,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode H,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode C,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode P,
        DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem DenseExtensionMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DenseExtensionMetricUp} :
    denseExtensionMetricToEventFlow x = denseExtensionMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      denseExtensionMetricFromEventFlow (denseExtensionMetricToEventFlow x) =
        denseExtensionMetricFromEventFlow (denseExtensionMetricToEventFlow y) :=
    congrArg denseExtensionMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DenseExtensionMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DenseExtensionMetricTasteGate_single_carrier_alignment_round_trip y)))

instance denseExtensionMetricBHistCarrier : BHistCarrier DenseExtensionMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := denseExtensionMetricToEventFlow
  fromEventFlow := denseExtensionMetricFromEventFlow

instance denseExtensionMetricChapterTasteGate : ChapterTasteGate DenseExtensionMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change denseExtensionMetricFromEventFlow (denseExtensionMetricToEventFlow x) = some x
    exact DenseExtensionMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DenseExtensionMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DenseExtensionMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, denseExtensionMetricDecodeBHist (denseExtensionMetricEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DenseExtensionMetricUp) ∧
        Nonempty (ChapterTasteGate DenseExtensionMetricUp) ∧
          denseExtensionMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DenseExtensionMetricTasteGate_single_carrier_alignment_decode_encode,
      ⟨denseExtensionMetricBHistCarrier⟩, ⟨denseExtensionMetricChapterTasteGate⟩, rfl⟩

end BEDC.Derived.DenseExtensionMetricUp
