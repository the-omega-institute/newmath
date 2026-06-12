import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuousFunctionCarrierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuousFunctionCarrierUp : Type where
  | mk (S F T M Q W R H C P N : BHist) : ContinuousFunctionCarrierUp
  deriving DecidableEq

def continuousFunctionCarrierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuousFunctionCarrierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuousFunctionCarrierEncodeBHist h

def continuousFunctionCarrierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuousFunctionCarrierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuousFunctionCarrierDecodeBHist tail)

private theorem continuousFunctionCarrier_decode_encode :
    ∀ h : BHist,
      continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuousFunctionCarrierFields : ContinuousFunctionCarrierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousFunctionCarrierUp.mk S F T M Q W R H C P N =>
      [S, F, T, M, Q, W, R, H, C, P, N]

def continuousFunctionCarrierToEventFlow : ContinuousFunctionCarrierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (continuousFunctionCarrierFields x).map continuousFunctionCarrierEncodeBHist

private def continuousFunctionCarrierEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuousFunctionCarrierEventAt index rest

def continuousFunctionCarrierFromEventFlow
    (ef : EventFlow) : Option ContinuousFunctionCarrierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuousFunctionCarrierUp.mk
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 0 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 1 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 2 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 3 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 4 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 5 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 6 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 7 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 8 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 9 ef))
      (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEventAt 10 ef)))

private theorem continuousFunctionCarrier_round_trip
    (x : ContinuousFunctionCarrierUp) :
    continuousFunctionCarrierFromEventFlow (continuousFunctionCarrierToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S F T M Q W R H C P N =>
      change
        some
          (ContinuousFunctionCarrierUp.mk
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist S))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist F))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist T))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist M))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist Q))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist W))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist R))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist H))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist C))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist P))
            (continuousFunctionCarrierDecodeBHist (continuousFunctionCarrierEncodeBHist N))) =
          some (ContinuousFunctionCarrierUp.mk S F T M Q W R H C P N)
      rw [continuousFunctionCarrier_decode_encode S,
        continuousFunctionCarrier_decode_encode F,
        continuousFunctionCarrier_decode_encode T,
        continuousFunctionCarrier_decode_encode M,
        continuousFunctionCarrier_decode_encode Q,
        continuousFunctionCarrier_decode_encode W,
        continuousFunctionCarrier_decode_encode R,
        continuousFunctionCarrier_decode_encode H,
        continuousFunctionCarrier_decode_encode C,
        continuousFunctionCarrier_decode_encode P,
        continuousFunctionCarrier_decode_encode N]

private theorem continuousFunctionCarrierToEventFlow_injective
    {x y : ContinuousFunctionCarrierUp} :
    continuousFunctionCarrierToEventFlow x = continuousFunctionCarrierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuousFunctionCarrierFromEventFlow (continuousFunctionCarrierToEventFlow x) =
        continuousFunctionCarrierFromEventFlow (continuousFunctionCarrierToEventFlow y) :=
    congrArg continuousFunctionCarrierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (continuousFunctionCarrier_round_trip x).symm
      (Eq.trans hread (continuousFunctionCarrier_round_trip y)))

instance continuousFunctionCarrierBHistCarrier :
    BHistCarrier ContinuousFunctionCarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuousFunctionCarrierToEventFlow
  fromEventFlow := continuousFunctionCarrierFromEventFlow

instance continuousFunctionCarrierChapterTasteGate :
    ChapterTasteGate ContinuousFunctionCarrierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuousFunctionCarrierFromEventFlow
      (continuousFunctionCarrierToEventFlow x) = some x
    exact continuousFunctionCarrier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuousFunctionCarrierToEventFlow_injective heq)

theorem ContinuousFunctionCarrierTasteGate_single_carrier_alignment :
    ChapterTasteGate ContinuousFunctionCarrierUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact continuousFunctionCarrierChapterTasteGate

end BEDC.Derived.ContinuousFunctionCarrierUp
