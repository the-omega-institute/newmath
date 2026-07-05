import BEDC.Derived.ClosedBetaPathUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.MetaCIC.ClosurePreservation

namespace BEDC.Derived.ClosedBetaPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.MetaCIC

theorem ClosedBetaPathCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {s t : Term} {n : Idx} {B K _H C _P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} (route : BetaStarStep s t)
    (closed_source : ClosedAt n s) (replay : Cont B K C) (named : PkgSig bundle N pkg) :
    ClosedAt n t ∧ Cont B K C ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig BEDC.MetaCIC
  exact ⟨betaStarStep_preserves_closed closed_source route, replay, named⟩

end BEDC.Derived.ClosedBetaPathUp
