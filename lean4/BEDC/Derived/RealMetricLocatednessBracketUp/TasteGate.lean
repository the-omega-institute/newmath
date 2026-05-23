import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealMetricLocatednessBracketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealMetricLocatednessBracketUp : Type where
  | mk (M L E S R D H C P N : BHist) : RealMetricLocatednessBracketUp
  deriving DecidableEq

def realMetricLocatednessBracketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realMetricLocatednessBracketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realMetricLocatednessBracketEncodeBHist h

def realMetricLocatednessBracketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realMetricLocatednessBracketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realMetricLocatednessBracketDecodeBHist tail)

private theorem realMetricLocatednessBracketDecode_encode :
    ∀ h : BHist,
      realMetricLocatednessBracketDecodeBHist
        (realMetricLocatednessBracketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realMetricLocatednessBracketToEventFlow : RealMetricLocatednessBracketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealMetricLocatednessBracketUp.mk M L E S R D H C P N =>
      [realMetricLocatednessBracketEncodeBHist M,
        realMetricLocatednessBracketEncodeBHist L,
        realMetricLocatednessBracketEncodeBHist E,
        realMetricLocatednessBracketEncodeBHist S,
        realMetricLocatednessBracketEncodeBHist R,
        realMetricLocatednessBracketEncodeBHist D,
        realMetricLocatednessBracketEncodeBHist H,
        realMetricLocatednessBracketEncodeBHist C,
        realMetricLocatednessBracketEncodeBHist P,
        realMetricLocatednessBracketEncodeBHist N]

private def realMetricLocatednessBracketEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realMetricLocatednessBracketEventAt index rest

def realMetricLocatednessBracketFromEventFlow (ef : EventFlow) :
    Option RealMetricLocatednessBracketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealMetricLocatednessBracketUp.mk
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 0 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 1 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 2 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 3 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 4 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 5 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 6 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 7 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 8 ef))
      (realMetricLocatednessBracketDecodeBHist (realMetricLocatednessBracketEventAt 9 ef)))

private theorem realMetricLocatednessBracket_round_trip :
    ∀ x : RealMetricLocatednessBracketUp,
      realMetricLocatednessBracketFromEventFlow
          (realMetricLocatednessBracketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M L E S R D H C P N =>
      change
        some
            (RealMetricLocatednessBracketUp.mk
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist M))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist L))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist E))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist S))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist R))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist D))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist H))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist C))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist P))
              (realMetricLocatednessBracketDecodeBHist
                (realMetricLocatednessBracketEncodeBHist N))) =
          some (RealMetricLocatednessBracketUp.mk M L E S R D H C P N)
      rw [realMetricLocatednessBracketDecode_encode M,
        realMetricLocatednessBracketDecode_encode L, realMetricLocatednessBracketDecode_encode E,
        realMetricLocatednessBracketDecode_encode S, realMetricLocatednessBracketDecode_encode R,
        realMetricLocatednessBracketDecode_encode D, realMetricLocatednessBracketDecode_encode H,
        realMetricLocatednessBracketDecode_encode C, realMetricLocatednessBracketDecode_encode P,
        realMetricLocatednessBracketDecode_encode N]

private theorem realMetricLocatednessBracketToEventFlow_injective
    {x y : RealMetricLocatednessBracketUp} :
    realMetricLocatednessBracketToEventFlow x = realMetricLocatednessBracketToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realMetricLocatednessBracketFromEventFlow
          (realMetricLocatednessBracketToEventFlow x) =
        realMetricLocatednessBracketFromEventFlow
          (realMetricLocatednessBracketToEventFlow y) :=
    congrArg realMetricLocatednessBracketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realMetricLocatednessBracket_round_trip x).symm
      (Eq.trans hread (realMetricLocatednessBracket_round_trip y)))

instance realMetricLocatednessBracketBHistCarrier :
    BHistCarrier RealMetricLocatednessBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realMetricLocatednessBracketToEventFlow
  fromEventFlow := realMetricLocatednessBracketFromEventFlow

instance realMetricLocatednessBracketChapterTasteGate :
    ChapterTasteGate RealMetricLocatednessBracketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realMetricLocatednessBracketFromEventFlow
          (realMetricLocatednessBracketToEventFlow x) =
        some x
    exact realMetricLocatednessBracket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realMetricLocatednessBracketToEventFlow_injective heq)

theorem RealMetricLocatednessBracketTasteGate_single_carrier_alignment :
    (forall h : BHist,
      realMetricLocatednessBracketDecodeBHist
        (realMetricLocatednessBracketEncodeBHist h) = h) ∧
      (forall x : RealMetricLocatednessBracketUp,
        realMetricLocatednessBracketFromEventFlow
            (realMetricLocatednessBracketToEventFlow x) =
          some x) ∧
        realMetricLocatednessBracketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact realMetricLocatednessBracketDecode_encode
  · constructor
    · exact realMetricLocatednessBracket_round_trip
    · rfl

def RealMetricLocatednessBracketCarrier [AskSetup] [PackageSetup]
    (metric locatedness equality windows readback tolerance transport replay provenance localName :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory metric ∧ UnaryHistory locatedness ∧ UnaryHistory equality ∧
    UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory tolerance ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem RealMetricLocatednessBracketCarrier_window_transport [AskSetup] [PackageSetup]
    {metric locatedness equality windows readback tolerance transport replay provenance localName
      metricRead locatednessRead equalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricLocatednessBracketCarrier metric locatedness equality windows readback tolerance
        transport replay provenance localName bundle pkg →
      Cont windows readback metricRead →
        Cont metricRead tolerance locatednessRead →
          Cont locatednessRead equality equalityRead →
            PkgSig bundle equalityRead pkg →
              UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory metricRead ∧
                UnaryHistory locatednessRead ∧ UnaryHistory equalityRead ∧
                  Cont windows readback metricRead ∧
                    Cont metricRead tolerance locatednessRead ∧
                      Cont locatednessRead equality equalityRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle equalityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowsReadback metricTolerance locatednessEquality equalitySig
  obtain ⟨_metricUnary, _locatednessUnary, equalityUnary, windowsUnary, readbackUnary,
    toleranceUnary, _transportUnary, _replayUnary, provenanceUnary, _localNameUnary,
    provenanceSig, _localNameSig⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed windowsUnary readbackUnary windowsReadback
  have locatednessReadUnary : UnaryHistory locatednessRead :=
    unary_cont_closed metricReadUnary toleranceUnary metricTolerance
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed locatednessReadUnary equalityUnary locatednessEquality
  exact
    ⟨windowsUnary, readbackUnary, metricReadUnary, locatednessReadUnary, equalityReadUnary,
      windowsReadback, metricTolerance, locatednessEquality, provenanceSig, equalitySig⟩

end BEDC.Derived.RealMetricLocatednessBracketUp
