import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealMetricLocatednessBracketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
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

theorem RealMetricLocatednessBracketCarrier_non_escape [AskSetup] [PackageSetup]
    {metric locatedness equality windows readback tolerance transport replay provenance localName
      metricRead locatednessRead equalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricLocatednessBracketCarrier metric locatedness equality windows readback tolerance
        transport replay provenance localName bundle pkg →
      Cont windows readback metricRead →
        Cont metricRead tolerance locatednessRead →
          Cont locatednessRead equality equalityRead →
            PkgSig bundle equalityRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row metric ∨ hsame row locatedness ∨ hsame row equality ∨
                      hsame row windows ∨ hsame row tolerance ∨ hsame row equalityRead)
                  (fun row : BHist =>
                    hsame row equalityRead ∧ PkgSig bundle equalityRead pkg)
                  hsame ∧
                UnaryHistory equalityRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier windowsReadback metricTolerance locatednessEquality equalitySig
  obtain ⟨_metricUnary, _locatednessUnary, equalityUnary, windowsUnary, readbackUnary,
    toleranceUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    provenanceSig, _localNameSig⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed windowsUnary readbackUnary windowsReadback
  have locatednessReadUnary : UnaryHistory locatednessRead :=
    unary_cont_closed metricReadUnary toleranceUnary metricTolerance
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed locatednessReadUnary equalityUnary locatednessEquality
  have sourceEquality :
      (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row) equalityRead := by
    exact ⟨hsame_refl equalityRead, equalityReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row equalityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row locatedness ∨ hsame row equality ∨
              hsame row windows ∨ hsame row tolerance ∨ hsame row equalityRead)
          (fun row : BHist => hsame row equalityRead ∧ PkgSig bundle equalityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro equalityRead sourceEquality
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, equalitySig⟩
  }
  exact ⟨cert, equalityReadUnary, provenanceSig⟩

theorem RealMetricLocatednessBracketNonEscape [AskSetup] [PackageSetup]
    {metric located equality stream readback dyadic transport replay provenance localName metricRead
      locatedRead equalityRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealMetricLocatednessBracketCarrier metric located equality stream readback dyadic transport replay
        provenance localName bundle pkg →
      Cont stream readback metricRead →
        Cont metricRead dyadic locatedRead →
          Cont locatedRead equality equalityRead →
            Cont equalityRead replay finalRead →
              PkgSig bundle finalRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row metric ∨ hsame row located ∨ hsame row equality ∨
                        hsame row stream ∨ hsame row readback ∨ hsame row dyadic ∨
                          hsame row finalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle finalRead pkg ∧
                        PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory metricRead ∧ UnaryHistory locatedRead ∧
                    UnaryHistory equalityRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier streamReadbackMetric metricDyadicLocated locatedEqualityRead
    equalityReplayFinal finalPkg
  obtain ⟨_metricUnary, _locatedUnary, equalityUnary, streamUnary, readbackUnary,
    dyadicUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    provenanceSig, _localNameSig⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed streamUnary readbackUnary streamReadbackMetric
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed metricReadUnary dyadicUnary metricDyadicLocated
  have equalityReadUnary : UnaryHistory equalityRead :=
    unary_cont_closed locatedReadUnary equalityUnary locatedEqualityRead
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed equalityReadUnary replayUnary equalityReplayFinal
  have sourceFinal :
      (fun row : BHist => hsame row finalRead ∧ UnaryHistory row) finalRead := by
    exact ⟨hsame_refl finalRead, finalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row located ∨ hsame row equality ∨
              hsame row stream ∨ hsame row readback ∨ hsame row dyadic ∨
                hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle finalRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead sourceFinal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, finalPkg, provenanceSig⟩
  }
  exact ⟨cert, metricReadUnary, locatedReadUnary, equalityReadUnary, finalReadUnary⟩

end BEDC.Derived.RealMetricLocatednessBracketUp
