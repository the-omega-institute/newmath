import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformTailComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformTailComparisonUp : Type where
  | mk
      (sourceLeft sourceRight windowLeft windowRight readbackLeft readbackRight dyadicLedger
        tailBudget sequenceLimit limsup transport replay provenance name : BHist) :
      RealUniformTailComparisonUp
  deriving DecidableEq

def realUniformTailComparisonEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformTailComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformTailComparisonEncodeBHist h

def realUniformTailComparisonDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformTailComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformTailComparisonDecodeBHist tail)

private theorem realUniformTailComparison_decode_encode :
    forall h : BHist,
      realUniformTailComparisonDecodeBHist (realUniformTailComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformTailComparisonToEventFlow : RealUniformTailComparisonUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformTailComparisonUp.mk sourceLeft sourceRight windowLeft windowRight readbackLeft
      readbackRight dyadicLedger tailBudget sequenceLimit limsup transport replay provenance
      name =>
      [[BMark.b0],
        realUniformTailComparisonEncodeBHist sourceLeft,
        [BMark.b1],
        realUniformTailComparisonEncodeBHist sourceRight,
        [BMark.b0, BMark.b0],
        realUniformTailComparisonEncodeBHist windowLeft,
        [BMark.b0, BMark.b1],
        realUniformTailComparisonEncodeBHist windowRight,
        [BMark.b1, BMark.b0],
        realUniformTailComparisonEncodeBHist readbackLeft,
        [BMark.b1, BMark.b1],
        realUniformTailComparisonEncodeBHist readbackRight,
        [BMark.b0, BMark.b0, BMark.b0],
        realUniformTailComparisonEncodeBHist dyadicLedger,
        [BMark.b0, BMark.b0, BMark.b1],
        realUniformTailComparisonEncodeBHist tailBudget,
        [BMark.b0, BMark.b1, BMark.b0],
        realUniformTailComparisonEncodeBHist sequenceLimit,
        [BMark.b0, BMark.b1, BMark.b1],
        realUniformTailComparisonEncodeBHist limsup,
        [BMark.b1, BMark.b0, BMark.b0],
        realUniformTailComparisonEncodeBHist transport,
        [BMark.b1, BMark.b0, BMark.b1],
        realUniformTailComparisonEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b0],
        realUniformTailComparisonEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1],
        realUniformTailComparisonEncodeBHist name]

private def realUniformTailComparisonEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => realUniformTailComparisonEventAtDefault index rest

private def realUniformTailComparisonLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => realUniformTailComparisonLengthEq n rest

def realUniformTailComparisonFromEventFlow : EventFlow -> Option RealUniformTailComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match realUniformTailComparisonLengthEq 28 flow with
      | true =>
          some
            (RealUniformTailComparisonUp.mk
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 1 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 3 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 5 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 7 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 9 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 11 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 13 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 15 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 17 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 19 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 21 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 23 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 25 flow))
              (realUniformTailComparisonDecodeBHist
                (realUniformTailComparisonEventAtDefault 27 flow)))
      | false => none

theorem RealUniformTailComparisonTasteGate_single_carrier_alignment_short_flow_rejected :
    realUniformTailComparisonFromEventFlow ([] : EventFlow) = none := by
  -- BEDC touchpoint anchor: BHist BMark
  rfl

private theorem realUniformTailComparison_round_trip :
    forall x : RealUniformTailComparisonUp,
      realUniformTailComparisonFromEventFlow
          (realUniformTailComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceLeft sourceRight windowLeft windowRight readbackLeft readbackRight dyadicLedger
      tailBudget sequenceLimit limsup transport replay provenance name =>
      change
        some
          (RealUniformTailComparisonUp.mk
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist sourceLeft))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist sourceRight))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist windowLeft))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist windowRight))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist readbackLeft))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist readbackRight))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist dyadicLedger))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist tailBudget))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist sequenceLimit))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist limsup))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist transport))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist replay))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist provenance))
            (realUniformTailComparisonDecodeBHist
              (realUniformTailComparisonEncodeBHist name))) =
          some
            (RealUniformTailComparisonUp.mk sourceLeft sourceRight windowLeft windowRight
              readbackLeft readbackRight dyadicLedger tailBudget sequenceLimit limsup
              transport replay provenance name)
      rw [realUniformTailComparison_decode_encode sourceLeft,
        realUniformTailComparison_decode_encode sourceRight,
        realUniformTailComparison_decode_encode windowLeft,
        realUniformTailComparison_decode_encode windowRight,
        realUniformTailComparison_decode_encode readbackLeft,
        realUniformTailComparison_decode_encode readbackRight,
        realUniformTailComparison_decode_encode dyadicLedger,
        realUniformTailComparison_decode_encode tailBudget,
        realUniformTailComparison_decode_encode sequenceLimit,
        realUniformTailComparison_decode_encode limsup,
        realUniformTailComparison_decode_encode transport,
        realUniformTailComparison_decode_encode replay,
        realUniformTailComparison_decode_encode provenance,
        realUniformTailComparison_decode_encode name]

private theorem realUniformTailComparisonToEventFlow_injective
    {x y : RealUniformTailComparisonUp} :
    realUniformTailComparisonToEventFlow x =
      realUniformTailComparisonToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformTailComparisonFromEventFlow (realUniformTailComparisonToEventFlow x) =
        realUniformTailComparisonFromEventFlow (realUniformTailComparisonToEventFlow y) :=
    congrArg realUniformTailComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realUniformTailComparison_round_trip x).symm
      (Eq.trans hread (realUniformTailComparison_round_trip y)))

instance realUniformTailComparisonBHistCarrier :
    BHistCarrier RealUniformTailComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformTailComparisonToEventFlow
  fromEventFlow := realUniformTailComparisonFromEventFlow

instance realUniformTailComparisonChapterTasteGate :
    ChapterTasteGate RealUniformTailComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realUniformTailComparisonFromEventFlow
        (realUniformTailComparisonToEventFlow x) = some x
    exact realUniformTailComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realUniformTailComparisonToEventFlow_injective heq)

theorem RealUniformTailComparisonTasteGate_single_carrier_alignment :
    (forall h : BHist,
      realUniformTailComparisonDecodeBHist (realUniformTailComparisonEncodeBHist h) = h) /\
      (forall x : RealUniformTailComparisonUp,
        realUniformTailComparisonFromEventFlow
          (realUniformTailComparisonToEventFlow x) = some x) /\
      (forall x y : RealUniformTailComparisonUp,
        realUniformTailComparisonToEventFlow x =
          realUniformTailComparisonToEventFlow y -> x = y) /\
      realUniformTailComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realUniformTailComparison_decode_encode,
      realUniformTailComparison_round_trip,
      (fun _ _ heq => realUniformTailComparisonToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RealUniformTailComparisonUp
