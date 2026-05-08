import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SeparableExtSourceSurface [AskSetup] [PackageSetup]
    (fieldExt polynomial generator minimal simpleRoot provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldExt ∧ UnaryHistory polynomial ∧ UnaryHistory generator ∧
    UnaryHistory minimal ∧ UnaryHistory simpleRoot ∧
      Cont fieldExt polynomial provenance ∧ Cont provenance simpleRoot endpoint ∧
        PkgSig bundle endpoint pkg

theorem SeparableExtSourceSurface_dependency_ledger_closure [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparableExtSourceSurface fieldExt polynomial generator minimal simpleRoot provenance endpoint
        bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        hsame provenance (append fieldExt polynomial) ∧
          hsame endpoint (append provenance simpleRoot) ∧ PkgSig bundle endpoint pkg := by
  intro surface
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed surface.left surface.right.left
      surface.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary surface.right.right.right.right.left
      surface.right.right.right.right.right.right.left
  exact And.intro provenanceUnary
    (And.intro endpointUnary
      (And.intro surface.right.right.right.right.right.left
        (And.intro surface.right.right.right.right.right.right.left
          surface.right.right.right.right.right.right.right)))

end BEDC.Derived.SeparableExtUp
