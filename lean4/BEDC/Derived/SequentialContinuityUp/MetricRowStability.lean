import BEDC.Derived.SequentialContinuityUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package

namespace BEDC.Derived.SequentialContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentialContinuityPacket [AskSetup] [PackageSetup]
    (MX MY F S L WX WY RX RY EX EY H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory MX ∧ UnaryHistory MY ∧ UnaryHistory F ∧ UnaryHistory S ∧
    UnaryHistory L ∧ UnaryHistory WX ∧ UnaryHistory WY ∧ UnaryHistory RX ∧
      UnaryHistory RY ∧ UnaryHistory EX ∧ UnaryHistory EY ∧ UnaryHistory H ∧
        UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont S L WX ∧
          Cont WX F WY ∧ Cont WX RX EX ∧ Cont WY RY EY ∧ Cont H C P ∧
            PkgSig bundle N pkg

theorem SequentialContinuityPacket_metric_row_stability [AskSetup] [PackageSetup]
    {MX MY F S L WX WY RX RY EX EY H C P N metricAudit metricReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialContinuityPacket MX MY F S L WX WY RX RY EX EY H C P N bundle pkg →
      Cont MX H metricAudit →
        Cont MY C metricReplay →
          PkgSig bundle metricReplay pkg →
            UnaryHistory MX ∧ UnaryHistory MY ∧ UnaryHistory H ∧ UnaryHistory C ∧
              UnaryHistory metricAudit ∧ UnaryHistory metricReplay ∧
                Cont MX H metricAudit ∧ Cont MY C metricReplay ∧
                  PkgSig bundle N pkg ∧ PkgSig bundle metricReplay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet metricAuditRoute metricReplayRoute metricReplayPkg
  have metricAuditUnary : UnaryHistory metricAudit :=
    unary_cont_closed packet.left packet.right.right.right.right.right.right.right.right.right.right.right.left
      metricAuditRoute
  have metricReplayUnary : UnaryHistory metricReplay :=
    unary_cont_closed packet.right.left
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left
      metricReplayRoute
  exact
    ⟨packet.left,
      packet.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.left,
      metricAuditUnary,
      metricReplayUnary,
      metricAuditRoute,
      metricReplayRoute,
      packet.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      metricReplayPkg⟩

end BEDC.Derived.SequentialContinuityUp
