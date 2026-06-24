import BEDC.Derived.KalmanFilterUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KalmanFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KalmanFilterUp : Type where
  | mk
      (estimate predicted covariancePrior covariance gain covariancePosterior transition input
        observation observationLedger predictionMap observationMap innovationMap gainMap
        estimateTransport matrixUpdate provenance endpoint : BHist) : KalmanFilterUp
  deriving DecidableEq

def kalmanFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kalmanFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kalmanFilterEncodeBHist h

def kalmanFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kalmanFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kalmanFilterDecodeBHist tail)

private theorem KalmanFilterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kalmanFilterDecodeBHist (kalmanFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kalmanFilterFields : KalmanFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KalmanFilterUp.mk estimate predicted covariancePrior covariance gain covariancePosterior
      transition input observation observationLedger predictionMap observationMap innovationMap
      gainMap estimateTransport matrixUpdate provenance endpoint =>
      [estimate, predicted, covariancePrior, covariance, gain, covariancePosterior, transition,
        input, observation, observationLedger, predictionMap, observationMap, innovationMap,
        gainMap, estimateTransport, matrixUpdate, provenance, endpoint]

def kalmanFilterToEventFlow : KalmanFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kalmanFilterFields x).map kalmanFilterEncodeBHist

private def kalmanFilterEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kalmanFilterEventAt index rest

def kalmanFilterFromEventFlow (ef : EventFlow) : Option KalmanFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KalmanFilterUp.mk
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 0 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 1 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 2 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 3 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 4 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 5 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 6 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 7 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 8 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 9 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 10 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 11 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 12 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 13 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 14 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 15 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 16 ef))
      (kalmanFilterDecodeBHist (kalmanFilterEventAt 17 ef)))

private theorem KalmanFilterTasteGate_single_carrier_alignment_round_trip
    (x : KalmanFilterUp) :
    kalmanFilterFromEventFlow (kalmanFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk estimate predicted covariancePrior covariance gain covariancePosterior transition input
      observation observationLedger predictionMap observationMap innovationMap gainMap
      estimateTransport matrixUpdate provenance endpoint =>
      change
        some
          (KalmanFilterUp.mk
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist estimate))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist predicted))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist covariancePrior))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist covariance))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist gain))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist covariancePosterior))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist transition))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist input))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist observation))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist observationLedger))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist predictionMap))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist observationMap))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist innovationMap))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist gainMap))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist estimateTransport))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist matrixUpdate))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist provenance))
            (kalmanFilterDecodeBHist (kalmanFilterEncodeBHist endpoint))) =
          some
            (KalmanFilterUp.mk estimate predicted covariancePrior covariance gain
              covariancePosterior transition input observation observationLedger predictionMap
              observationMap innovationMap gainMap estimateTransport matrixUpdate provenance
              endpoint)
      rw [KalmanFilterTasteGate_single_carrier_alignment_decode_encode estimate,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode predicted,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode covariancePrior,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode covariance,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode gain,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode covariancePosterior,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode transition,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode input,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode observation,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode observationLedger,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode predictionMap,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode observationMap,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode innovationMap,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode gainMap,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode estimateTransport,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode matrixUpdate,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode provenance,
        KalmanFilterTasteGate_single_carrier_alignment_decode_encode endpoint]

private theorem KalmanFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KalmanFilterUp} :
    kalmanFilterToEventFlow x = kalmanFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kalmanFilterFromEventFlow (kalmanFilterToEventFlow x) =
        kalmanFilterFromEventFlow (kalmanFilterToEventFlow y) :=
    congrArg kalmanFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KalmanFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KalmanFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem KalmanFilterTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : KalmanFilterUp, kalmanFilterFields x = kalmanFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk estimate₁ predicted₁ covariancePrior₁ covariance₁ gain₁ covariancePosterior₁ transition₁
      input₁ observation₁ observationLedger₁ predictionMap₁ observationMap₁ innovationMap₁
      gainMap₁ estimateTransport₁ matrixUpdate₁ provenance₁ endpoint₁ =>
      cases y with
      | mk estimate₂ predicted₂ covariancePrior₂ covariance₂ gain₂ covariancePosterior₂
          transition₂ input₂ observation₂ observationLedger₂ predictionMap₂ observationMap₂
          innovationMap₂ gainMap₂ estimateTransport₂ matrixUpdate₂ provenance₂ endpoint₂ =>
          cases hfields
          rfl

instance kalmanFilterBHistCarrier : BHistCarrier KalmanFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kalmanFilterToEventFlow
  fromEventFlow := kalmanFilterFromEventFlow

instance kalmanFilterChapterTasteGate : ChapterTasteGate KalmanFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kalmanFilterFromEventFlow (kalmanFilterToEventFlow x) = some x
    exact KalmanFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KalmanFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance kalmanFilterFieldFaithful : FieldFaithful KalmanFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kalmanFilterFields
  field_faithful := KalmanFilterTasteGate_single_carrier_alignment_field_faithful

instance kalmanFilterNontrivial :
    BEDC.Meta.TasteGate.Nontrivial KalmanFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KalmanFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KalmanFilterUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem KalmanFilterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KalmanFilterUp) ∧
      Nonempty (FieldFaithful KalmanFilterUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial KalmanFilterUp) ∧
          (∀ h : BHist, kalmanFilterDecodeBHist (kalmanFilterEncodeBHist h) = h) ∧
            (∀ x : KalmanFilterUp,
              kalmanFilterFromEventFlow (kalmanFilterToEventFlow x) = some x) ∧
              kalmanFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨kalmanFilterChapterTasteGate⟩, ⟨kalmanFilterFieldFaithful⟩,
      ⟨kalmanFilterNontrivial⟩,
      KalmanFilterTasteGate_single_carrier_alignment_decode_encode,
      KalmanFilterTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.KalmanFilterUp
