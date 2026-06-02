import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DirichletSeriesTestUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DirichletSeriesTestUp : Type where
  | mk
      (realSeries uniformCauchy limitInterface ratReadback streamWindow dyadicTolerance
        endpointSeal partialSumLedger coefficientLedger abelVariation transport replay provenance
        localName : BHist) : DirichletSeriesTestUp

def dirichletSeriesTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dirichletSeriesTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dirichletSeriesTestEncodeBHist h

def dirichletSeriesTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dirichletSeriesTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dirichletSeriesTestDecodeBHist tail)

private theorem DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dirichletSeriesTestFields : DirichletSeriesTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DirichletSeriesTestUp.mk realSeries uniformCauchy limitInterface ratReadback streamWindow
      dyadicTolerance endpointSeal partialSumLedger coefficientLedger abelVariation transport replay
      provenance localName =>
      [realSeries, uniformCauchy, limitInterface, ratReadback, streamWindow, dyadicTolerance,
        endpointSeal, partialSumLedger, coefficientLedger, abelVariation, transport, replay,
        provenance, localName]

def dirichletSeriesTestToEventFlow : DirichletSeriesTestUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dirichletSeriesTestFields x).map dirichletSeriesTestEncodeBHist

private def dirichletSeriesTestEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dirichletSeriesTestEventAtDefault index rest

def dirichletSeriesTestFromEventFlow (ef : EventFlow) : Option DirichletSeriesTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DirichletSeriesTestUp.mk
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 0 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 1 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 2 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 3 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 4 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 5 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 6 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 7 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 8 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 9 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 10 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 11 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 12 ef))
      (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEventAtDefault 13 ef)))

private theorem DirichletSeriesTestTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DirichletSeriesTestUp,
      dirichletSeriesTestFromEventFlow (dirichletSeriesTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk realSeries uniformCauchy limitInterface ratReadback streamWindow dyadicTolerance
      endpointSeal partialSumLedger coefficientLedger abelVariation transport replay provenance
      localName =>
      change
        some
          (DirichletSeriesTestUp.mk
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist realSeries))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist uniformCauchy))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist limitInterface))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist ratReadback))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist streamWindow))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist dyadicTolerance))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist endpointSeal))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist partialSumLedger))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist coefficientLedger))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist abelVariation))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist transport))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist replay))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist provenance))
            (dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist localName))) =
          some
            (DirichletSeriesTestUp.mk realSeries uniformCauchy limitInterface ratReadback
              streamWindow dyadicTolerance endpointSeal partialSumLedger coefficientLedger
              abelVariation transport replay provenance localName)
      rw [DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode realSeries,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode uniformCauchy,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode limitInterface,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode ratReadback,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode streamWindow,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode dyadicTolerance,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode endpointSeal,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode partialSumLedger,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode coefficientLedger,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode abelVariation,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode transport,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode replay,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode provenance,
        DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode localName]

private theorem DirichletSeriesTestTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DirichletSeriesTestUp} :
    dirichletSeriesTestToEventFlow x = dirichletSeriesTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dirichletSeriesTestFromEventFlow (dirichletSeriesTestToEventFlow x) =
        dirichletSeriesTestFromEventFlow (dirichletSeriesTestToEventFlow y) :=
    congrArg dirichletSeriesTestFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DirichletSeriesTestTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DirichletSeriesTestTasteGate_single_carrier_alignment_round_trip y)))

instance dirichletSeriesTestBHistCarrier : BHistCarrier DirichletSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dirichletSeriesTestToEventFlow
  fromEventFlow := dirichletSeriesTestFromEventFlow

instance dirichletSeriesTestChapterTasteGate : ChapterTasteGate DirichletSeriesTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dirichletSeriesTestFromEventFlow (dirichletSeriesTestToEventFlow x) = some x
    exact DirichletSeriesTestTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DirichletSeriesTestTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DirichletSeriesTestTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DirichletSeriesTestUp) ∧
      Nonempty (ChapterTasteGate DirichletSeriesTestUp) ∧
        (∀ h : BHist, dirichletSeriesTestDecodeBHist (dirichletSeriesTestEncodeBHist h) = h) ∧
          dirichletSeriesTestEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨dirichletSeriesTestBHistCarrier⟩, ⟨dirichletSeriesTestChapterTasteGate⟩,
      DirichletSeriesTestTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.DirichletSeriesTestUp
