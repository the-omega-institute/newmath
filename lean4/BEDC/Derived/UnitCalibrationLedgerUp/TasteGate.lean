import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnitCalibrationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnitCalibrationLedgerUp : Type where
  | mk :
      (measurement unitBridge calibration uncertainty instrument reproducibility dimension
        classifier transport provenance name : BHist) →
      UnitCalibrationLedgerUp
  deriving DecidableEq

def unitCalibrationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unitCalibrationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unitCalibrationLedgerEncodeBHist h

def unitCalibrationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unitCalibrationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unitCalibrationLedgerDecodeBHist tail)

private theorem unitCalibrationLedger_decode_encode_bhist :
    ∀ h : BHist,
      unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def unitCalibrationLedgerFields : UnitCalibrationLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UnitCalibrationLedgerUp.mk measurement unitBridge calibration uncertainty instrument
      reproducibility dimension classifier transport provenance name =>
      [measurement, unitBridge, calibration, uncertainty, instrument, reproducibility,
        dimension, classifier, transport, provenance, name]

def unitCalibrationLedgerToEventFlow : UnitCalibrationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (unitCalibrationLedgerFields x).map unitCalibrationLedgerEncodeBHist

def unitCalibrationLedgerFromEventFlow : EventFlow → Option UnitCalibrationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [measurement, unitBridge, calibration, uncertainty, instrument, reproducibility,
      dimension, classifier, transport, provenance, name] =>
      some
        (UnitCalibrationLedgerUp.mk
          (unitCalibrationLedgerDecodeBHist measurement)
          (unitCalibrationLedgerDecodeBHist unitBridge)
          (unitCalibrationLedgerDecodeBHist calibration)
          (unitCalibrationLedgerDecodeBHist uncertainty)
          (unitCalibrationLedgerDecodeBHist instrument)
          (unitCalibrationLedgerDecodeBHist reproducibility)
          (unitCalibrationLedgerDecodeBHist dimension)
          (unitCalibrationLedgerDecodeBHist classifier)
          (unitCalibrationLedgerDecodeBHist transport)
          (unitCalibrationLedgerDecodeBHist provenance)
          (unitCalibrationLedgerDecodeBHist name))
  | _ => none

private theorem unitCalibrationLedger_round_trip :
    ∀ x : UnitCalibrationLedgerUp,
      unitCalibrationLedgerFromEventFlow
        (unitCalibrationLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk measurement unitBridge calibration uncertainty instrument reproducibility dimension
      classifier transport provenance name =>
      change
        some
          (UnitCalibrationLedgerUp.mk
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist measurement))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist unitBridge))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist calibration))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist uncertainty))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist instrument))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist reproducibility))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist dimension))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist classifier))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist transport))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist provenance))
            (unitCalibrationLedgerDecodeBHist
              (unitCalibrationLedgerEncodeBHist name))) =
          some
            (UnitCalibrationLedgerUp.mk measurement unitBridge calibration uncertainty
              instrument reproducibility dimension classifier transport provenance name)
      rw [unitCalibrationLedger_decode_encode_bhist measurement,
        unitCalibrationLedger_decode_encode_bhist unitBridge,
        unitCalibrationLedger_decode_encode_bhist calibration,
        unitCalibrationLedger_decode_encode_bhist uncertainty,
        unitCalibrationLedger_decode_encode_bhist instrument,
        unitCalibrationLedger_decode_encode_bhist reproducibility,
        unitCalibrationLedger_decode_encode_bhist dimension,
        unitCalibrationLedger_decode_encode_bhist classifier,
        unitCalibrationLedger_decode_encode_bhist transport,
        unitCalibrationLedger_decode_encode_bhist provenance,
        unitCalibrationLedger_decode_encode_bhist name]

private theorem unitCalibrationLedgerToEventFlow_injective
    {x y : UnitCalibrationLedgerUp} :
    unitCalibrationLedgerToEventFlow x = unitCalibrationLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow x) =
        unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow y) :=
    congrArg unitCalibrationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (unitCalibrationLedger_round_trip x).symm
      (Eq.trans hread (unitCalibrationLedger_round_trip y)))

private theorem unitCalibrationLedger_fields_faithful :
    ∀ x y : UnitCalibrationLedgerUp,
      unitCalibrationLedgerFields x = unitCalibrationLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk measurement₁ unitBridge₁ calibration₁ uncertainty₁ instrument₁ reproducibility₁
      dimension₁ classifier₁ transport₁ provenance₁ name₁ =>
      cases y with
      | mk measurement₂ unitBridge₂ calibration₂ uncertainty₂ instrument₂ reproducibility₂
          dimension₂ classifier₂ transport₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance unitCalibrationLedgerBHistCarrier :
    BHistCarrier UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unitCalibrationLedgerToEventFlow
  fromEventFlow := unitCalibrationLedgerFromEventFlow

instance unitCalibrationLedgerChapterTasteGate :
    ChapterTasteGate UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      unitCalibrationLedgerFromEventFlow
        (unitCalibrationLedgerToEventFlow x) = some x
    exact unitCalibrationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unitCalibrationLedgerToEventFlow_injective heq)

instance unitCalibrationLedgerFieldFaithful :
    FieldFaithful UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := unitCalibrationLedgerFields
  field_faithful := unitCalibrationLedger_fields_faithful

instance unitCalibrationLedgerNontrivial :
    Nontrivial UnitCalibrationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UnitCalibrationLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UnitCalibrationLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UnitCalibrationLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  unitCalibrationLedgerChapterTasteGate

end BEDC.Derived.UnitCalibrationLedgerUp
