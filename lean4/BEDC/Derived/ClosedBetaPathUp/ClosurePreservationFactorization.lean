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

theorem ClosedBetaPathCarrier_closure_preservation_factorization [AskSetup] [PackageSetup]
    {s t : Term} {n : Idx} {B K C N downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} (route : BetaStarStep s t)
    (closed_source : ClosedAt n s) (replay : Cont B K C)
    (handoff : Cont K downstream N) (named : PkgSig bundle N pkg) :
    ClosedAt n t ∧ Cont B K C ∧ Cont K downstream N ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig BEDC.MetaCIC
  exact ⟨betaStarStep_preserves_closed closed_source route, replay, handoff, named⟩

end BEDC.Derived.ClosedBetaPathUp
