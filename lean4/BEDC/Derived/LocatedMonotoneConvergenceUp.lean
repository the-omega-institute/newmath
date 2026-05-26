import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedMonotoneConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedMonotoneConvergenceCarrier [AskSetup] [PackageSetup]
    (monotone bounded located window readback dyadic realSeal transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory monotone ∧ UnaryHistory bounded ∧ UnaryHistory located ∧
    UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont monotone bounded located ∧
          Cont located window readback ∧ Cont readback dyadic realSeal ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem LocatedMonotoneConvergenceCarrier_supremum_readback [AskSetup] [PackageSetup]
    {monotone bounded located window readback dyadic realSeal transport replay provenance
      localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedMonotoneConvergenceCarrier monotone bounded located window readback dyadic realSeal
        transport replay provenance localName bundle pkg ->
      Cont readback dyadic consumer ->
        PkgSig bundle consumer pkg ->
          hsame consumer realSeal ∧ UnaryHistory located ∧ UnaryHistory window ∧
            UnaryHistory readback ∧ UnaryHistory dyadic ∧ UnaryHistory realSeal ∧
              UnaryHistory consumer ∧ Cont located window readback ∧
                Cont readback dyadic realSeal ∧ Cont readback dyadic consumer ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory PkgSig
  intro carrier readbackDyadicConsumer consumerPkg
  obtain ⟨_monotoneUnary, _boundedUnary, locatedUnary, windowUnary, readbackUnary,
    dyadicUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _monotoneBoundedLocated, locatedWindowReadback,
    readbackDyadicRealSeal, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
    carrier
  have consumerSameRealSeal : hsame consumer realSeal :=
    cont_deterministic readbackDyadicConsumer readbackDyadicRealSeal
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadicConsumer
  exact
    ⟨consumerSameRealSeal, locatedUnary, windowUnary, readbackUnary, dyadicUnary, realSealUnary,
      consumerUnary, locatedWindowReadback, readbackDyadicRealSeal, readbackDyadicConsumer,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.LocatedMonotoneConvergenceUp
