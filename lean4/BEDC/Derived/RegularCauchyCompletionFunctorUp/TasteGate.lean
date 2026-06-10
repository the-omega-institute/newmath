import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionFunctorUp : Type where
  | mk
      (metricSource uniformlyContinuousMap finiteWindow dyadicTolerance regSeqReadback
        realSeal identityLedger compositionLedger transport replay provenance localName :
        BHist) :
      RegularCauchyCompletionFunctorUp
  deriving DecidableEq

def regularCauchyCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionFunctorEncodeBHist h

def regularCauchyCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionFunctorDecodeBHist tail)

private theorem RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCompletionFunctorDecodeBHist
          (regularCauchyCompletionFunctorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionFunctorToEventFlow :
    RegularCauchyCompletionFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionFunctorUp.mk metricSource uniformlyContinuousMap finiteWindow
      dyadicTolerance regSeqReadback realSeal identityLedger compositionLedger transport replay
      provenance localName =>
      [regularCauchyCompletionFunctorEncodeBHist metricSource,
        regularCauchyCompletionFunctorEncodeBHist uniformlyContinuousMap,
        regularCauchyCompletionFunctorEncodeBHist finiteWindow,
        regularCauchyCompletionFunctorEncodeBHist dyadicTolerance,
        regularCauchyCompletionFunctorEncodeBHist regSeqReadback,
        regularCauchyCompletionFunctorEncodeBHist realSeal,
        regularCauchyCompletionFunctorEncodeBHist identityLedger,
        regularCauchyCompletionFunctorEncodeBHist compositionLedger,
        regularCauchyCompletionFunctorEncodeBHist transport,
        regularCauchyCompletionFunctorEncodeBHist replay,
        regularCauchyCompletionFunctorEncodeBHist provenance,
        regularCauchyCompletionFunctorEncodeBHist localName]

private def regularCauchyCompletionFunctorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCompletionFunctorEventAt index rest

def regularCauchyCompletionFunctorFromEventFlow (ef : EventFlow) :
    Option RegularCauchyCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCompletionFunctorUp.mk
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 0 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 1 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 2 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 3 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 4 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 5 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 6 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 7 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 8 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 9 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 10 ef))
      (regularCauchyCompletionFunctorDecodeBHist
        (regularCauchyCompletionFunctorEventAt 11 ef)))

private theorem RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCompletionFunctorUp,
      regularCauchyCompletionFunctorFromEventFlow
          (regularCauchyCompletionFunctorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metricSource uniformlyContinuousMap finiteWindow dyadicTolerance regSeqReadback realSeal
      identityLedger compositionLedger transport replay provenance localName =>
      change
        some
          (RegularCauchyCompletionFunctorUp.mk
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist metricSource))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist uniformlyContinuousMap))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist finiteWindow))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist dyadicTolerance))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist regSeqReadback))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist realSeal))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist identityLedger))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist compositionLedger))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist transport))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist replay))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist provenance))
            (regularCauchyCompletionFunctorDecodeBHist
              (regularCauchyCompletionFunctorEncodeBHist localName))) =
          some
            (RegularCauchyCompletionFunctorUp.mk metricSource uniformlyContinuousMap finiteWindow
              dyadicTolerance regSeqReadback realSeal identityLedger compositionLedger transport
              replay provenance localName)
      rw [RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode metricSource,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode
          uniformlyContinuousMap,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode finiteWindow,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode dyadicTolerance,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode regSeqReadback,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode realSeal,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode identityLedger,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode
          compositionLedger,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode transport,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode replay,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode provenance,
        RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode localName]

private theorem RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyCompletionFunctorUp} :
    regularCauchyCompletionFunctorToEventFlow x =
      regularCauchyCompletionFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionFunctorFromEventFlow
          (regularCauchyCompletionFunctorToEventFlow x) =
        regularCauchyCompletionFunctorFromEventFlow
          (regularCauchyCompletionFunctorToEventFlow y) :=
    congrArg regularCauchyCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyCompletionFunctorBHistCarrier :
    BHistCarrier RegularCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionFunctorToEventFlow
  fromEventFlow := regularCauchyCompletionFunctorFromEventFlow

instance regularCauchyCompletionFunctorChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionFunctorFromEventFlow
          (regularCauchyCompletionFunctorToEventFlow x) =
        some x
    exact RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_injective heq)

def RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionFunctorChapterTasteGate

theorem RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionFunctorDecodeBHist
          (regularCauchyCompletionFunctorEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyCompletionFunctorUp,
        regularCauchyCompletionFunctorFromEventFlow
            (regularCauchyCompletionFunctorToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyCompletionFunctorUp,
        regularCauchyCompletionFunctorToEventFlow x =
            regularCauchyCompletionFunctorToEventFlow y →
          x = y) ∧
      regularCauchyCompletionFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RegularCauchyCompletionFunctorTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.RegularCauchyCompletionFunctorUp
