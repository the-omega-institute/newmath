import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuityCalibrationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContinuityCalibrationUp : Type where
  | mk (S M U W R D E H C P N : BHist) : CauchyContinuityCalibrationUp
  deriving DecidableEq

def cauchyContinuityCalibrationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuityCalibrationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuityCalibrationEncodeBHist h

def cauchyContinuityCalibrationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuityCalibrationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuityCalibrationDecodeBHist tail)

private theorem cauchyContinuityCalibration_decode_encode :
    ∀ h : BHist,
      cauchyContinuityCalibrationDecodeBHist
          (cauchyContinuityCalibrationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContinuityCalibrationFields :
    CauchyContinuityCalibrationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuityCalibrationUp.mk S M U W R D E H C P N =>
      [S, M, U, W, R, D, E, H, C, P, N]

def cauchyContinuityCalibrationToEventFlow :
    CauchyContinuityCalibrationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyContinuityCalibrationFields x).map cauchyContinuityCalibrationEncodeBHist

private def cauchyContinuityCalibrationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyContinuityCalibrationEventAt index rest

def cauchyContinuityCalibrationFromEventFlow
    (ef : EventFlow) : Option CauchyContinuityCalibrationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyContinuityCalibrationUp.mk
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 0 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 1 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 2 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 3 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 4 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 5 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 6 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 7 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 8 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 9 ef))
      (cauchyContinuityCalibrationDecodeBHist
        (cauchyContinuityCalibrationEventAt 10 ef)))

private theorem cauchyContinuityCalibration_round_trip
    (x : CauchyContinuityCalibrationUp) :
    cauchyContinuityCalibrationFromEventFlow
        (cauchyContinuityCalibrationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M U W R D E H C P N =>
      change
        some
          (CauchyContinuityCalibrationUp.mk
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist S))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist M))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist U))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist W))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist R))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist D))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist E))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist H))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist C))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist P))
            (cauchyContinuityCalibrationDecodeBHist
              (cauchyContinuityCalibrationEncodeBHist N))) =
          some (CauchyContinuityCalibrationUp.mk S M U W R D E H C P N)
      rw [cauchyContinuityCalibration_decode_encode S,
        cauchyContinuityCalibration_decode_encode M,
        cauchyContinuityCalibration_decode_encode U,
        cauchyContinuityCalibration_decode_encode W,
        cauchyContinuityCalibration_decode_encode R,
        cauchyContinuityCalibration_decode_encode D,
        cauchyContinuityCalibration_decode_encode E,
        cauchyContinuityCalibration_decode_encode H,
        cauchyContinuityCalibration_decode_encode C,
        cauchyContinuityCalibration_decode_encode P,
        cauchyContinuityCalibration_decode_encode N]

private theorem cauchyContinuityCalibrationToEventFlow_injective
    {x y : CauchyContinuityCalibrationUp} :
    cauchyContinuityCalibrationToEventFlow x =
        cauchyContinuityCalibrationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuityCalibrationFromEventFlow
          (cauchyContinuityCalibrationToEventFlow x) =
        cauchyContinuityCalibrationFromEventFlow
          (cauchyContinuityCalibrationToEventFlow y) :=
    congrArg cauchyContinuityCalibrationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyContinuityCalibration_round_trip x).symm
      (Eq.trans hread (cauchyContinuityCalibration_round_trip y)))

instance cauchyContinuityCalibrationBHistCarrier :
    BHistCarrier CauchyContinuityCalibrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuityCalibrationToEventFlow
  fromEventFlow := cauchyContinuityCalibrationFromEventFlow

instance cauchyContinuityCalibrationChapterTasteGate :
    ChapterTasteGate CauchyContinuityCalibrationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyContinuityCalibrationFromEventFlow
      (cauchyContinuityCalibrationToEventFlow x) = some x
    exact cauchyContinuityCalibration_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyContinuityCalibrationToEventFlow_injective heq)

theorem CauchyContinuityCalibrationTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyContinuityCalibrationUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact cauchyContinuityCalibrationChapterTasteGate

end BEDC.Derived.CauchyContinuityCalibrationUp
