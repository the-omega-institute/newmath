import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ContinuationReplayUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContinuationReplayCarrier [AskSetup] [PackageSetup]
    (S T E H C P N start terminal replay : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory E ∧ UnaryHistory H ∧
    UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory start ∧
      hsame terminal terminal ∧ hsame replay replay ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem ContinuationReplayCarrier_endpoint_transport [AskSetup] [PackageSetup]
    {S T E H C P N start terminal replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationReplayCarrier S T E H C P N start terminal replay bundle pkg ->
      Cont start S replay ->
        Cont replay E terminal ->
          UnaryHistory replay ∧ UnaryHistory terminal ∧ Cont start S replay ∧
            Cont replay E terminal ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier startRoute terminalRoute
  obtain ⟨unaryS, _unaryT, unaryE, _unaryH, _unaryC, _unaryP, _unaryN,
    unaryStart, _terminalSame, _replaySame, pkgP, pkgN⟩ := carrier
  have unaryReplay : UnaryHistory replay :=
    unary_cont_closed unaryStart unaryS startRoute
  have unaryTerminal : UnaryHistory terminal :=
    unary_cont_closed unaryReplay unaryE terminalRoute
  exact ⟨unaryReplay, unaryTerminal, startRoute, terminalRoute, pkgP, pkgN⟩

end BEDC.Derived.ContinuationReplayUp
