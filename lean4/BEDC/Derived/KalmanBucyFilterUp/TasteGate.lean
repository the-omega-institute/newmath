import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KalmanBucyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KalmanBucyFilterUp : Type where
  | mk
      (state observation stateFlow observationFlow processCovariance measurementCovariance
        riccati gain estimator stateReplay observationReplay innovation siblingReadback transport
        replay provenance name : BHist) : KalmanBucyFilterUp
  deriving DecidableEq

def kalmanBucyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kalmanBucyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kalmanBucyFilterEncodeBHist h

def kalmanBucyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kalmanBucyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kalmanBucyFilterDecodeBHist tail)

private theorem KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kalmanBucyFilterFields : KalmanBucyFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KalmanBucyFilterUp.mk state observation stateFlow observationFlow processCovariance
      measurementCovariance riccati gain estimator stateReplay observationReplay innovation
      siblingReadback transport replay provenance name =>
      [state, observation, stateFlow, observationFlow, processCovariance,
        measurementCovariance, riccati, gain, estimator, stateReplay, observationReplay,
        innovation, siblingReadback, transport, replay, provenance, name]

def kalmanBucyFilterToEventFlow : KalmanBucyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kalmanBucyFilterFields x).map kalmanBucyFilterEncodeBHist

private def kalmanBucyFilterEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kalmanBucyFilterEventAt index rest

def kalmanBucyFilterFromEventFlow (ef : EventFlow) : Option KalmanBucyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KalmanBucyFilterUp.mk
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 0 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 1 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 2 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 3 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 4 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 5 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 6 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 7 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 8 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 9 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 10 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 11 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 12 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 13 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 14 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 15 ef))
      (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEventAt 16 ef)))

private theorem KalmanBucyFilterTasteGate_single_carrier_alignment_round_trip
    (x : KalmanBucyFilterUp) :
    kalmanBucyFilterFromEventFlow (kalmanBucyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk state observation stateFlow observationFlow processCovariance measurementCovariance
      riccati gain estimator stateReplay observationReplay innovation siblingReadback transport
      replay provenance name =>
      change
        some
            (KalmanBucyFilterUp.mk
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist state))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist observation))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist stateFlow))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist observationFlow))
              (kalmanBucyFilterDecodeBHist
                (kalmanBucyFilterEncodeBHist processCovariance))
              (kalmanBucyFilterDecodeBHist
                (kalmanBucyFilterEncodeBHist measurementCovariance))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist riccati))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist gain))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist estimator))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist stateReplay))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist observationReplay))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist innovation))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist siblingReadback))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist transport))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist replay))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist provenance))
              (kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist name))) =
          some
            (KalmanBucyFilterUp.mk state observation stateFlow observationFlow
              processCovariance measurementCovariance riccati gain estimator stateReplay
              observationReplay innovation siblingReadback transport replay provenance name)
      rw [KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode state,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode observation,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode stateFlow,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode observationFlow,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode processCovariance,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode measurementCovariance,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode riccati,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode gain,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode estimator,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode stateReplay,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode observationReplay,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode innovation,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode siblingReadback,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode transport,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode replay,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode provenance,
        KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode name]

private theorem KalmanBucyFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KalmanBucyFilterUp} :
    kalmanBucyFilterToEventFlow x = kalmanBucyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kalmanBucyFilterFromEventFlow (kalmanBucyFilterToEventFlow x) =
        kalmanBucyFilterFromEventFlow (kalmanBucyFilterToEventFlow y) :=
    congrArg kalmanBucyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KalmanBucyFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KalmanBucyFilterTasteGate_single_carrier_alignment_round_trip y)))

instance kalmanBucyFilterBHistCarrier : BHistCarrier KalmanBucyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kalmanBucyFilterToEventFlow
  fromEventFlow := kalmanBucyFilterFromEventFlow

instance kalmanBucyFilterChapterTasteGate : ChapterTasteGate KalmanBucyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kalmanBucyFilterFromEventFlow (kalmanBucyFilterToEventFlow x) = some x
    exact KalmanBucyFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KalmanBucyFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem KalmanBucyFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, kalmanBucyFilterDecodeBHist (kalmanBucyFilterEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KalmanBucyFilterUp) ∧
        Nonempty (ChapterTasteGate KalmanBucyFilterUp) ∧
          kalmanBucyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨KalmanBucyFilterTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨kalmanBucyFilterBHistCarrier⟩,
        ⟨⟨kalmanBucyFilterChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.KalmanBucyFilterUp
