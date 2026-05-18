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

private theorem unitCalibrationLedger_mk_congr
    {measurement measurement' unitBridge unitBridge' calibration calibration'
      uncertainty uncertainty' instrument instrument' reproducibility reproducibility'
      dimension dimension' classifier classifier' transport transport' provenance provenance'
      name name' : BHist}
    (hMeasurement : measurement' = measurement)
    (hUnitBridge : unitBridge' = unitBridge)
    (hCalibration : calibration' = calibration)
    (hUncertainty : uncertainty' = uncertainty)
    (hInstrument : instrument' = instrument)
    (hReproducibility : reproducibility' = reproducibility)
    (hDimension : dimension' = dimension)
    (hClassifier : classifier' = classifier)
    (hTransport : transport' = transport)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    UnitCalibrationLedgerUp.mk measurement' unitBridge' calibration' uncertainty' instrument'
        reproducibility' dimension' classifier' transport' provenance' name' =
      UnitCalibrationLedgerUp.mk measurement unitBridge calibration uncertainty instrument
        reproducibility dimension classifier transport provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMeasurement
  cases hUnitBridge
  cases hCalibration
  cases hUncertainty
  cases hInstrument
  cases hReproducibility
  cases hDimension
  cases hClassifier
  cases hTransport
  cases hProvenance
  cases hName
  rfl

private theorem unitCalibrationLedgerEncodeBHist_injective {h k : BHist} :
    unitCalibrationLedgerEncodeBHist h = unitCalibrationLedgerEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  exact
    Eq.trans (unitCalibrationLedger_decode_encode_bhist h).symm
      (Eq.trans (congrArg unitCalibrationLedgerDecodeBHist heq)
        (unitCalibrationLedger_decode_encode_bhist k))

def unitCalibrationLedgerFields : UnitCalibrationLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UnitCalibrationLedgerUp.mk measurement unitBridge calibration uncertainty instrument
      reproducibility dimension classifier transport provenance name =>
      [measurement, unitBridge, calibration, uncertainty, instrument, reproducibility,
        dimension, classifier, transport, provenance, name]

def unitCalibrationLedgerToEventFlow : UnitCalibrationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UnitCalibrationLedgerUp.mk measurement unitBridge calibration uncertainty instrument
      reproducibility dimension classifier transport provenance name =>
      [[BMark.b0],
        unitCalibrationLedgerEncodeBHist measurement,
        [BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist unitBridge,
        [BMark.b1, BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist calibration,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist uncertainty,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist instrument,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist reproducibility,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist dimension,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        unitCalibrationLedgerEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        unitCalibrationLedgerEncodeBHist name]

private def unitCalibrationLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => unitCalibrationLedgerRawAt n rest

private def unitCalibrationLedgerLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => unitCalibrationLedgerLengthEq n rest

def unitCalibrationLedgerFromEventFlow : EventFlow → Option UnitCalibrationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match unitCalibrationLedgerLengthEq 22 flow with
      | true =>
          some
            (UnitCalibrationLedgerUp.mk
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 1 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 3 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 5 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 7 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 9 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 11 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 13 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 15 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 17 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 19 flow))
              (unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerRawAt 21 flow)))
      | false => none

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
      exact
        congrArg some
          (unitCalibrationLedger_mk_congr
            (unitCalibrationLedger_decode_encode_bhist measurement)
            (unitCalibrationLedger_decode_encode_bhist unitBridge)
            (unitCalibrationLedger_decode_encode_bhist calibration)
            (unitCalibrationLedger_decode_encode_bhist uncertainty)
            (unitCalibrationLedger_decode_encode_bhist instrument)
            (unitCalibrationLedger_decode_encode_bhist reproducibility)
            (unitCalibrationLedger_decode_encode_bhist dimension)
            (unitCalibrationLedger_decode_encode_bhist classifier)
            (unitCalibrationLedger_decode_encode_bhist transport)
            (unitCalibrationLedger_decode_encode_bhist provenance)
            (unitCalibrationLedger_decode_encode_bhist name))

private theorem unitCalibrationLedgerToEventFlow_injective
    {x y : UnitCalibrationLedgerUp} :
    unitCalibrationLedgerToEventFlow x = unitCalibrationLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow x) =
        unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow y) :=
    congrArg unitCalibrationLedgerFromEventFlow heq
  have hsome :
      some x = some y :=
    Eq.trans (unitCalibrationLedger_round_trip x).symm
      (Eq.trans hread (unitCalibrationLedger_round_trip y))
  cases hsome
  rfl

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

theorem UnitCalibrationLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, unitCalibrationLedgerDecodeBHist (unitCalibrationLedgerEncodeBHist h) = h) ∧
      (∀ x : UnitCalibrationLedgerUp,
        unitCalibrationLedgerFromEventFlow (unitCalibrationLedgerToEventFlow x) = some x) ∧
        (∀ x y : UnitCalibrationLedgerUp,
          unitCalibrationLedgerToEventFlow x = unitCalibrationLedgerToEventFlow y → x = y) ∧
          unitCalibrationLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact unitCalibrationLedger_decode_encode_bhist
  · constructor
    · intro x
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
          exact
            congrArg some
              (unitCalibrationLedger_mk_congr
                (unitCalibrationLedger_decode_encode_bhist measurement)
                (unitCalibrationLedger_decode_encode_bhist unitBridge)
                (unitCalibrationLedger_decode_encode_bhist calibration)
                (unitCalibrationLedger_decode_encode_bhist uncertainty)
                (unitCalibrationLedger_decode_encode_bhist instrument)
                (unitCalibrationLedger_decode_encode_bhist reproducibility)
                (unitCalibrationLedger_decode_encode_bhist dimension)
                (unitCalibrationLedger_decode_encode_bhist classifier)
                (unitCalibrationLedger_decode_encode_bhist transport)
                (unitCalibrationLedger_decode_encode_bhist provenance)
                (unitCalibrationLedger_decode_encode_bhist name))
    · constructor
      · intro x y heq
        exact unitCalibrationLedgerToEventFlow_injective heq
      · rfl

end BEDC.Derived.UnitCalibrationLedgerUp
