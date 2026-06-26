import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionMinimalityUp : Type where
  | mk (X C E U F S H R P N : BHist) : CauchyCompletionMinimalityUp
  deriving DecidableEq

private def cauchyCompletionMinimalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionMinimalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionMinimalityEncodeBHist h

private def cauchyCompletionMinimalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionMinimalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionMinimalityDecodeBHist tail)

private theorem CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionMinimalityDecodeBHist
        (cauchyCompletionMinimalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def CauchyCompletionMinimalityTasteGate_single_carrier_alignment_fields :
    CauchyCompletionMinimalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionMinimalityUp.mk X C E U F S H R P N =>
      [X, C, E, U, F, S, H, R, P, N]

private def cauchyCompletionMinimalityToEventFlow :
    CauchyCompletionMinimalityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyCompletionMinimalityTasteGate_single_carrier_alignment_fields x).map
      cauchyCompletionMinimalityEncodeBHist

private def cauchyCompletionMinimalityEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionMinimalityEventAtDefault index rest

private def cauchyCompletionMinimalityFromEventFlow :
    EventFlow → Option CauchyCompletionMinimalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionMinimalityUp.mk
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 0 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 1 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 2 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 3 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 4 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 5 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 6 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 7 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 8 ef))
        (cauchyCompletionMinimalityDecodeBHist
          (cauchyCompletionMinimalityEventAtDefault 9 ef)))

private theorem CauchyCompletionMinimalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionMinimalityUp,
      cauchyCompletionMinimalityFromEventFlow
        (cauchyCompletionMinimalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X C E U F S H R P N =>
      change
        some
          (CauchyCompletionMinimalityUp.mk
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist X))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist C))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist E))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist U))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist F))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist S))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist H))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist R))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist P))
            (cauchyCompletionMinimalityDecodeBHist
              (cauchyCompletionMinimalityEncodeBHist N))) =
          some (CauchyCompletionMinimalityUp.mk X C E U F S H R P N)
      rw [CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode X,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode U,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode F,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode R,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompletionMinimalityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionMinimalityUp} :
    cauchyCompletionMinimalityToEventFlow x =
      cauchyCompletionMinimalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionMinimalityFromEventFlow
          (cauchyCompletionMinimalityToEventFlow x) =
        cauchyCompletionMinimalityFromEventFlow
          (cauchyCompletionMinimalityToEventFlow y) :=
    congrArg cauchyCompletionMinimalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionMinimalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionMinimalityTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionMinimalityBHistCarrier :
    BHistCarrier CauchyCompletionMinimalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionMinimalityToEventFlow
  fromEventFlow := cauchyCompletionMinimalityFromEventFlow

instance cauchyCompletionMinimalityChapterTasteGate :
    ChapterTasteGate CauchyCompletionMinimalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionMinimalityFromEventFlow
        (cauchyCompletionMinimalityToEventFlow x) = some x
    exact CauchyCompletionMinimalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionMinimalityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyCompletionMinimalityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionMinimalityDecodeBHist
        (cauchyCompletionMinimalityEncodeBHist h) = h) ∧
      CauchyCompletionMinimalityTasteGate_single_carrier_alignment_fields
        (CauchyCompletionMinimalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact CauchyCompletionMinimalityTasteGate_single_carrier_alignment_decode_encode
  · rfl

def CauchyCompletionMinimalityCarrier [AskSetup] [PackageSetup]
    (source completion embedding universal extension separated transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory source ∧ UnaryHistory completion ∧ UnaryHistory embedding ∧
    UnaryHistory universal ∧ UnaryHistory extension ∧ UnaryHistory separated ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont completion embedding universal ∧
          Cont universal extension separated ∧ PkgSig bundle provenance pkg

theorem CauchyCompletionMinimalityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead compared : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg →
      Cont completion embedding denseRead →
        Cont extension separated compared →
          UnaryHistory source ∧ UnaryHistory completion ∧ UnaryHistory embedding ∧
            UnaryHistory universal ∧ UnaryHistory extension ∧ UnaryHistory separated ∧
              UnaryHistory denseRead ∧ UnaryHistory compared ∧
                Cont completion embedding denseRead ∧ Cont extension separated compared ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier denseRoute comparedRoute
  obtain ⟨sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _universalRoute, _separatedRoute, provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary embeddingUnary denseRoute
  have comparedUnary : UnaryHistory compared :=
    unary_cont_closed extensionUnary separatedUnary comparedRoute
  exact
    ⟨sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
      separatedUnary, denseUnary, comparedUnary, denseRoute, comparedRoute, provenancePkg⟩

end BEDC.Derived.CauchyCompletionMinimalityUp
