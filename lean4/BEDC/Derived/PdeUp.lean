import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PdeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PdeCarriedSourceRow [AskSetup] [PackageSetup]
    (manifold derivative relation boundary endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory derivative ∧ UnaryHistory boundary ∧
    Cont manifold derivative relation ∧ Cont relation boundary endpoint ∧
      PkgSig bundle endpoint pkg

theorem PdeCarriedSourceRow_carrier_obligation [AskSetup] [PackageSetup]
    {manifold derivative relation boundary endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PdeCarriedSourceRow manifold derivative relation boundary endpoint bundle pkg ->
      UnaryHistory relation ∧ UnaryHistory endpoint ∧ Cont manifold derivative relation ∧
        Cont relation boundary endpoint ∧ PkgSig bundle endpoint pkg := by
  intro row
  have relationUnary : UnaryHistory relation :=
    unary_cont_closed row.left row.right.left row.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed relationUnary row.right.right.left row.right.right.right.right.left
  exact And.intro relationUnary
    (And.intro endpointUnary
      (And.intro row.right.right.right.left
        (And.intro row.right.right.right.right.left row.right.right.right.right.right)))

end BEDC.Derived.PdeUp
