import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GoldenMeanShiftUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GoldenMeanShiftUp : Type where
  | mk : (window zeroWitness adjacency provenance ledger : BHist) → GoldenMeanShiftUp

def goldenMeanShiftEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: goldenMeanShiftEncodeBHist h
  | BHist.e1 h => BMark.b1 :: goldenMeanShiftEncodeBHist h

def goldenMeanShiftDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (goldenMeanShiftDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (goldenMeanShiftDecodeBHist tail)

private theorem goldenMeanShiftDecode_encode_bhist :
    ∀ h : BHist, goldenMeanShiftDecodeBHist (goldenMeanShiftEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem goldenMeanShift_mk_congr
    {window window' zeroWitness zeroWitness' adjacency adjacency' provenance provenance'
      ledger ledger' : BHist}
    (hWindow : window' = window)
    (hZeroWitness : zeroWitness' = zeroWitness)
    (hAdjacency : adjacency' = adjacency)
    (hProvenance : provenance' = provenance)
    (hLedger : ledger' = ledger) :
    GoldenMeanShiftUp.mk window' zeroWitness' adjacency' provenance' ledger' =
      GoldenMeanShiftUp.mk window zeroWitness adjacency provenance ledger := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hWindow
  cases hZeroWitness
  cases hAdjacency
  cases hProvenance
  cases hLedger
  rfl

def goldenMeanShiftToEventFlow : GoldenMeanShiftUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GoldenMeanShiftUp.mk window zeroWitness adjacency provenance ledger =>
      [[BMark.b0],
        goldenMeanShiftEncodeBHist window,
        [BMark.b1, BMark.b0],
        goldenMeanShiftEncodeBHist zeroWitness,
        [BMark.b1, BMark.b1, BMark.b0],
        goldenMeanShiftEncodeBHist adjacency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        goldenMeanShiftEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        goldenMeanShiftEncodeBHist ledger]

def goldenMeanShiftFromEventFlow : EventFlow → Option GoldenMeanShiftUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: window :: _tag1 :: zeroWitness :: _tag2 :: adjacency :: _tag3 ::
      provenance :: _tag4 :: ledger :: [] =>
      some
        (GoldenMeanShiftUp.mk
          (goldenMeanShiftDecodeBHist window)
          (goldenMeanShiftDecodeBHist zeroWitness)
          (goldenMeanShiftDecodeBHist adjacency)
          (goldenMeanShiftDecodeBHist provenance)
          (goldenMeanShiftDecodeBHist ledger))
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

private theorem goldenMeanShift_round_trip :
    ∀ x : GoldenMeanShiftUp,
      goldenMeanShiftFromEventFlow (goldenMeanShiftToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window zeroWitness adjacency provenance ledger =>
      change
        some
          (GoldenMeanShiftUp.mk
            (goldenMeanShiftDecodeBHist (goldenMeanShiftEncodeBHist window))
            (goldenMeanShiftDecodeBHist (goldenMeanShiftEncodeBHist zeroWitness))
            (goldenMeanShiftDecodeBHist (goldenMeanShiftEncodeBHist adjacency))
            (goldenMeanShiftDecodeBHist (goldenMeanShiftEncodeBHist provenance))
            (goldenMeanShiftDecodeBHist (goldenMeanShiftEncodeBHist ledger))) =
          some (GoldenMeanShiftUp.mk window zeroWitness adjacency provenance ledger)
      exact
        congrArg some
          (goldenMeanShift_mk_congr
            (goldenMeanShiftDecode_encode_bhist window)
            (goldenMeanShiftDecode_encode_bhist zeroWitness)
            (goldenMeanShiftDecode_encode_bhist adjacency)
            (goldenMeanShiftDecode_encode_bhist provenance)
            (goldenMeanShiftDecode_encode_bhist ledger))

private theorem goldenMeanShiftToEventFlow_injective (x y : GoldenMeanShiftUp) :
    goldenMeanShiftToEventFlow x = goldenMeanShiftToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      goldenMeanShiftFromEventFlow (goldenMeanShiftToEventFlow x) =
        goldenMeanShiftFromEventFlow (goldenMeanShiftToEventFlow y) :=
    congrArg goldenMeanShiftFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (goldenMeanShift_round_trip x).symm
      (Eq.trans hread (goldenMeanShift_round_trip y)))

instance goldenMeanShiftBHistCarrier : BHistCarrier GoldenMeanShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := goldenMeanShiftToEventFlow
  fromEventFlow := goldenMeanShiftFromEventFlow

instance goldenMeanShiftChapterTasteGate : ChapterTasteGate GoldenMeanShiftUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change goldenMeanShiftFromEventFlow (goldenMeanShiftToEventFlow x) = some x
    exact goldenMeanShift_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (goldenMeanShiftToEventFlow_injective x y heq)

def taste_gate : ChapterTasteGate GoldenMeanShiftUp :=
  -- BEDC touchpoint anchor: BHist BMark
  goldenMeanShiftChapterTasteGate

theorem GoldenMeanShiftTasteGate_single_carrier_alignment :
    (∀ h : BHist, goldenMeanShiftDecodeBHist (goldenMeanShiftEncodeBHist h) = h) ∧
      (∀ x : GoldenMeanShiftUp,
        goldenMeanShiftFromEventFlow (goldenMeanShiftToEventFlow x) = some x) ∧
      (∀ x y : GoldenMeanShiftUp,
        goldenMeanShiftToEventFlow x = goldenMeanShiftToEventFlow y → x = y) ∧
      goldenMeanShiftEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    And.intro goldenMeanShiftDecode_encode_bhist
      (And.intro goldenMeanShift_round_trip
        (And.intro
          (fun x y heq => goldenMeanShiftToEventFlow_injective x y heq)
          rfl))

end BEDC.Derived.GoldenMeanShiftUp
