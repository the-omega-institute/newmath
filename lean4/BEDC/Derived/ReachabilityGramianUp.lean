import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# ReachabilityGramianUp finite carrier.
-/

namespace BEDC.Derived.ReachabilityGramianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ReachabilityGramianBHistCarrier [AskSetup] [PackageSetup]
    (transition control horizon gramian transport route provenance cert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory transition ∧ UnaryHistory control ∧ UnaryHistory horizon ∧
    UnaryHistory gramian ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧ UnaryHistory endpoint ∧
        Cont transport route endpoint ∧ PkgSig bundle endpoint pkg

theorem ReachabilityGramianBHistCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {transition control horizon gramian transport route provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ReachabilityGramianBHistCarrier transition control horizon gramian transport route provenance
        cert endpoint bundle pkg ->
      UnaryHistory transition /\ UnaryHistory control /\ UnaryHistory horizon /\
        UnaryHistory gramian /\ UnaryHistory transport /\ UnaryHistory route /\
          UnaryHistory provenance /\ UnaryHistory cert /\ UnaryHistory endpoint /\
            Cont transport route endpoint /\ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    provenanceUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩ := carrier
  exact ⟨transitionUnary, controlUnary, horizonUnary, gramianUnary, transportUnary, routeUnary,
    provenanceUnary, certUnary, endpointUnary, endpointRoute, endpointPkg⟩

end BEDC.Derived.ReachabilityGramianUp
