import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionStabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def RegularCauchyCompletionStabilityCarrier [AskSetup] [PackageSetup]
    (Q W D R E H C P N sealRead witnessRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory Q ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ UnaryHistory sealRead ∧ UnaryHistory witnessRead ∧
        Cont Q W D ∧ Cont D R sealRead ∧ Cont sealRead E witnessRead ∧
          PkgSig bundle P pkg

theorem RegularCauchyCompletionStabilityCarrier_idempotence_boundary [AskSetup]
    [PackageSetup]
    {Q W D R E H C P N sealRead witnessRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionStabilityCarrier Q W D R E H C P N sealRead witnessRead
        bundle pkg →
      Cont witnessRead C replayRead →
        PkgSig bundle replayRead pkg →
          UnaryHistory Q ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
            UnaryHistory E ∧ UnaryHistory sealRead ∧ UnaryHistory witnessRead ∧
              UnaryHistory replayRead ∧ Cont Q W D ∧ Cont D R sealRead ∧
                Cont sealRead E witnessRead ∧ Cont witnessRead C replayRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier witnessReplay replayPkg
  obtain ⟨qUnary, wUnary, dUnary, rUnary, eUnary, _hUnary, cUnary, _pUnary, _nUnary,
    sealUnary, witnessUnary, qWindowDyadic, dyadicRealSeal, sealWitness,
    provenancePkg⟩ := carrier
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed witnessUnary cUnary witnessReplay
  exact
    ⟨qUnary, wUnary, dUnary, rUnary, eUnary, sealUnary, witnessUnary, replayUnary,
      qWindowDyadic, dyadicRealSeal, sealWitness, witnessReplay, provenancePkg, replayPkg⟩

inductive RegularCauchyCompletionStabilityUp : Type where
  | mk (Q W D R E H C P N : BHist) : RegularCauchyCompletionStabilityUp
  deriving DecidableEq

def regularCauchyCompletionStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionStabilityEncodeBHist h

def regularCauchyCompletionStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionStabilityDecodeBHist tail)

private theorem regularCauchyCompletionStabilityDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyCompletionStabilityToEventFlow :
    RegularCauchyCompletionStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionStabilityUp.mk Q W D R E H C P N =>
      [[BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist Q,
        [BMark.b1, BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyCompletionStabilityEncodeBHist N]

private def regularCauchyCompletionStabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyCompletionStabilityEventAtDefault index rest

def regularCauchyCompletionStabilityFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCompletionStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCompletionStabilityUp.mk
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 1 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 3 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 5 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 7 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 9 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 11 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 13 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 15 ef))
      (regularCauchyCompletionStabilityDecodeBHist
        (regularCauchyCompletionStabilityEventAtDefault 17 ef)))

private theorem regularCauchyCompletionStability_round_trip
    (x : RegularCauchyCompletionStabilityUp) :
    regularCauchyCompletionStabilityFromEventFlow
      (regularCauchyCompletionStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk Q W D R E H C P N =>
      change
        some
          (RegularCauchyCompletionStabilityUp.mk
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist Q))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist W))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist D))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist R))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist E))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist H))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist C))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist P))
            (regularCauchyCompletionStabilityDecodeBHist
              (regularCauchyCompletionStabilityEncodeBHist N))) =
          some (RegularCauchyCompletionStabilityUp.mk Q W D R E H C P N)
      rw [regularCauchyCompletionStabilityDecode_encode_bhist Q,
        regularCauchyCompletionStabilityDecode_encode_bhist W,
        regularCauchyCompletionStabilityDecode_encode_bhist D,
        regularCauchyCompletionStabilityDecode_encode_bhist R,
        regularCauchyCompletionStabilityDecode_encode_bhist E,
        regularCauchyCompletionStabilityDecode_encode_bhist H,
        regularCauchyCompletionStabilityDecode_encode_bhist C,
        regularCauchyCompletionStabilityDecode_encode_bhist P,
        regularCauchyCompletionStabilityDecode_encode_bhist N]

private theorem regularCauchyCompletionStabilityToEventFlow_injective
    {x y : RegularCauchyCompletionStabilityUp} :
    regularCauchyCompletionStabilityToEventFlow x =
      regularCauchyCompletionStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionStabilityFromEventFlow
          (regularCauchyCompletionStabilityToEventFlow x) =
        regularCauchyCompletionStabilityFromEventFlow
          (regularCauchyCompletionStabilityToEventFlow y) :=
    congrArg regularCauchyCompletionStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCompletionStability_round_trip x).symm
      (Eq.trans hread (regularCauchyCompletionStability_round_trip y)))

instance regularCauchyCompletionStabilityBHistCarrier :
    BHistCarrier RegularCauchyCompletionStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionStabilityToEventFlow
  fromEventFlow := regularCauchyCompletionStabilityFromEventFlow

instance regularCauchyCompletionStabilityChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionStabilityFromEventFlow
        (regularCauchyCompletionStabilityToEventFlow x) = some x
    exact regularCauchyCompletionStability_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionStabilityToEventFlow_injective heq)

theorem RegularCauchyCompletionStabilityNameCertObligations :
    Nonempty (BHistCarrier RegularCauchyCompletionStabilityUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyCompletionStabilityUp) ∧
        regularCauchyCompletionStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BEDC.
  exact
    ⟨Nonempty.intro regularCauchyCompletionStabilityBHistCarrier,
      Nonempty.intro regularCauchyCompletionStabilityChapterTasteGate, rfl⟩

end BEDC.Derived.RegularCauchyCompletionStabilityUp
