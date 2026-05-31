import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricBallUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricBallUp : Type where
  | mk (X d c r rho m H C P N : BHist) : MetricBallUp
  deriving DecidableEq

def metricBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricBallEncodeBHist h

def metricBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricBallDecodeBHist tail)

private theorem metricBall_decode_encode_bhist :
    ∀ h : BHist, metricBallDecodeBHist (metricBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metricBallFields : MetricBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetricBallUp.mk X d c r rho m H C P N => [X, d, c, r, rho, m, H, C, P, N]

def metricBallToEventFlow : MetricBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricBallUp.mk X d c r rho m H C P N =>
      [metricBallEncodeBHist X,
        metricBallEncodeBHist d,
        metricBallEncodeBHist c,
        metricBallEncodeBHist r,
        metricBallEncodeBHist rho,
        metricBallEncodeBHist m,
        metricBallEncodeBHist H,
        metricBallEncodeBHist C,
        metricBallEncodeBHist P,
        metricBallEncodeBHist N]

private def metricBallRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => metricBallRawAt n rest

private def metricBallLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => metricBallLengthEq n rest

def metricBallFromEventFlow : EventFlow → Option MetricBallUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match metricBallLengthEq 10 flow with
      | true =>
          some
            (MetricBallUp.mk
              (metricBallDecodeBHist (metricBallRawAt 0 flow))
              (metricBallDecodeBHist (metricBallRawAt 1 flow))
              (metricBallDecodeBHist (metricBallRawAt 2 flow))
              (metricBallDecodeBHist (metricBallRawAt 3 flow))
              (metricBallDecodeBHist (metricBallRawAt 4 flow))
              (metricBallDecodeBHist (metricBallRawAt 5 flow))
              (metricBallDecodeBHist (metricBallRawAt 6 flow))
              (metricBallDecodeBHist (metricBallRawAt 7 flow))
              (metricBallDecodeBHist (metricBallRawAt 8 flow))
              (metricBallDecodeBHist (metricBallRawAt 9 flow)))
      | false => none

private theorem metricBall_round_trip :
    ∀ x : MetricBallUp,
      metricBallFromEventFlow (metricBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d c r rho m H C P N =>
      change
        some
          (MetricBallUp.mk
            (metricBallDecodeBHist (metricBallEncodeBHist X))
            (metricBallDecodeBHist (metricBallEncodeBHist d))
            (metricBallDecodeBHist (metricBallEncodeBHist c))
            (metricBallDecodeBHist (metricBallEncodeBHist r))
            (metricBallDecodeBHist (metricBallEncodeBHist rho))
            (metricBallDecodeBHist (metricBallEncodeBHist m))
            (metricBallDecodeBHist (metricBallEncodeBHist H))
            (metricBallDecodeBHist (metricBallEncodeBHist C))
            (metricBallDecodeBHist (metricBallEncodeBHist P))
            (metricBallDecodeBHist (metricBallEncodeBHist N))) =
          some (MetricBallUp.mk X d c r rho m H C P N)
      rw [metricBall_decode_encode_bhist X,
        metricBall_decode_encode_bhist d,
        metricBall_decode_encode_bhist c,
        metricBall_decode_encode_bhist r,
        metricBall_decode_encode_bhist rho,
        metricBall_decode_encode_bhist m,
        metricBall_decode_encode_bhist H,
        metricBall_decode_encode_bhist C,
        metricBall_decode_encode_bhist P,
        metricBall_decode_encode_bhist N]

private theorem metricBallToEventFlow_injective {x y : MetricBallUp} :
    metricBallToEventFlow x = metricBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metricBallFromEventFlow (metricBallToEventFlow x) =
        metricBallFromEventFlow (metricBallToEventFlow y) :=
    congrArg metricBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metricBall_round_trip x).symm
      (Eq.trans hread (metricBall_round_trip y)))

instance metricBallBHistCarrier : BHistCarrier MetricBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricBallToEventFlow
  fromEventFlow := metricBallFromEventFlow

instance metricBallChapterTasteGate : ChapterTasteGate MetricBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metricBallFromEventFlow (metricBallToEventFlow x) = some x
    exact metricBall_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricBallToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MetricBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metricBallChapterTasteGate

theorem MetricBallTasteGate_single_carrier_alignment :
    (∀ h : BHist, metricBallDecodeBHist (metricBallEncodeBHist h) = h) ∧
      metricBallFields
          (MetricBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨metricBall_decode_encode_bhist, rfl⟩

end BEDC.Derived.MetricBallUp
