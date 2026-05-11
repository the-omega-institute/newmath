import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VonneumannalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def VonNeumannAlgBHistCarrier [AskSetup] [PackageSetup]
    (cstar hilbert operator adjoint multiplication weakTest weakProbe provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory cstar ∧ UnaryHistory hilbert ∧ UnaryHistory operator ∧
    UnaryHistory adjoint ∧ UnaryHistory multiplication ∧ UnaryHistory weakTest ∧
      UnaryHistory weakProbe ∧ UnaryHistory provenance ∧ Cont cstar operator adjoint ∧
        Cont operator multiplication provenance ∧ Cont hilbert weakProbe weakTest ∧
          Cont weakTest operator endpoint ∧ PkgSig bundle endpoint pkg

theorem VonNeumannAlgBHistCarrier_weak_operator_ledger_exactness [AskSetup] [PackageSetup]
    {cstar hilbert operator adjoint multiplication weakTest weakProbe provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    VonNeumannAlgBHistCarrier cstar hilbert operator adjoint multiplication weakTest weakProbe
        provenance endpoint bundle pkg ->
      UnaryHistory weakTest ∧ UnaryHistory weakProbe ∧ Cont hilbert weakProbe weakTest ∧
        Cont weakTest operator endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have weakTestUnary : UnaryHistory weakTest :=
    carrier.right.right.right.right.right.left
  have weakProbeUnary : UnaryHistory weakProbe :=
    carrier.right.right.right.right.right.right.left
  have weakProbeRow : Cont hilbert weakProbe weakTest :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont weakTest operator endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.left
  have packageRow : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  exact And.intro weakTestUnary
    (And.intro weakProbeUnary
      (And.intro weakProbeRow (And.intro endpointRow packageRow)))

end BEDC.Derived.VonneumannalgebraUp
