import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWindowCompactnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWindowCompactnessUp : Type where
  | mk :
      (compactSource metricDistance dyadicRadius intervalSource finiteGrid lowerBound
        uniformModulus transport replay provenance localName : BHist) →
      FiniteWindowCompactnessUp
  deriving DecidableEq

def finiteWindowCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWindowCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWindowCompactnessEncodeBHist h

def finiteWindowCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWindowCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWindowCompactnessDecodeBHist tail)

private theorem finiteWindowCompactness_decode_encode :
    ∀ h : BHist,
      finiteWindowCompactnessDecodeBHist
        (finiteWindowCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteWindowCompactnessFields :
    FiniteWindowCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWindowCompactnessUp.mk compactSource metricDistance dyadicRadius intervalSource
      finiteGrid lowerBound uniformModulus transport replay provenance localName =>
      [compactSource, metricDistance, dyadicRadius, intervalSource, finiteGrid,
        lowerBound, uniformModulus, transport, replay, provenance, localName]

def finiteWindowCompactnessToEventFlow :
    FiniteWindowCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteWindowCompactnessFields x).map finiteWindowCompactnessEncodeBHist

private def finiteWindowCompactnessEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteWindowCompactnessEventAtDefault index rest

def finiteWindowCompactnessFromEventFlow
    (ef : EventFlow) : Option FiniteWindowCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteWindowCompactnessUp.mk
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 0 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 1 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 2 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 3 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 4 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 5 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 6 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 7 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 8 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 9 ef))
      (finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEventAtDefault 10 ef)))

private theorem finiteWindowCompactness_round_trip
    (x : FiniteWindowCompactnessUp) :
    finiteWindowCompactnessFromEventFlow
      (finiteWindowCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk compactSource metricDistance dyadicRadius intervalSource finiteGrid lowerBound
      uniformModulus transport replay provenance localName =>
      change
        some
          (FiniteWindowCompactnessUp.mk
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist compactSource))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist metricDistance))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist dyadicRadius))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist intervalSource))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist finiteGrid))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist lowerBound))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist uniformModulus))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist transport))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist replay))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist provenance))
            (finiteWindowCompactnessDecodeBHist
              (finiteWindowCompactnessEncodeBHist localName))) =
          some
            (FiniteWindowCompactnessUp.mk compactSource metricDistance dyadicRadius
              intervalSource finiteGrid lowerBound uniformModulus transport replay
              provenance localName)
      rw [finiteWindowCompactness_decode_encode compactSource,
        finiteWindowCompactness_decode_encode metricDistance,
        finiteWindowCompactness_decode_encode dyadicRadius,
        finiteWindowCompactness_decode_encode intervalSource,
        finiteWindowCompactness_decode_encode finiteGrid,
        finiteWindowCompactness_decode_encode lowerBound,
        finiteWindowCompactness_decode_encode uniformModulus,
        finiteWindowCompactness_decode_encode transport,
        finiteWindowCompactness_decode_encode replay,
        finiteWindowCompactness_decode_encode provenance,
        finiteWindowCompactness_decode_encode localName]

private theorem finiteWindowCompactnessToEventFlow_injective
    {x y : FiniteWindowCompactnessUp} :
    finiteWindowCompactnessToEventFlow x =
      finiteWindowCompactnessToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWindowCompactnessFromEventFlow (finiteWindowCompactnessToEventFlow x) =
        finiteWindowCompactnessFromEventFlow (finiteWindowCompactnessToEventFlow y) :=
    congrArg finiteWindowCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (finiteWindowCompactness_round_trip x).symm
      (Eq.trans hread (finiteWindowCompactness_round_trip y)))

instance finiteWindowCompactnessBHistCarrier :
    BHistCarrier FiniteWindowCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWindowCompactnessToEventFlow
  fromEventFlow := finiteWindowCompactnessFromEventFlow

instance finiteWindowCompactnessChapterTasteGate :
    ChapterTasteGate FiniteWindowCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteWindowCompactnessFromEventFlow
        (finiteWindowCompactnessToEventFlow x) = some x
    exact finiteWindowCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteWindowCompactnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteWindowCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteWindowCompactnessChapterTasteGate

theorem FiniteWindowCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        finiteWindowCompactnessDecodeBHist (finiteWindowCompactnessEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FiniteWindowCompactnessUp) ∧
        Nonempty (ChapterTasteGate FiniteWindowCompactnessUp) ∧
          finiteWindowCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteWindowCompactness_decode_encode,
      ⟨finiteWindowCompactnessBHistCarrier⟩,
      ⟨finiteWindowCompactnessChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FiniteWindowCompactnessUp
