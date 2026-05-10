import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.PartitionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PartitionBHistCarrier [AskSetup] [PackageSetup]
    (list parts sum weakDecrease boundary routes provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory list ∧ UnaryHistory parts ∧ UnaryHistory sum ∧
    UnaryHistory weakDecrease ∧ UnaryHistory boundary ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont list parts sum ∧
        Cont sum weakDecrease boundary ∧ Cont boundary routes provenance ∧
          PkgSig bundle endpoint pkg

theorem PartitionBHistCarrier_obligation [AskSetup] [PackageSetup]
    {list parts sum weakDecrease boundary routes provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PartitionBHistCarrier list parts sum weakDecrease boundary routes provenance endpoint
        bundle pkg ->
      UnaryHistory list ∧ UnaryHistory parts ∧ UnaryHistory sum ∧
        UnaryHistory weakDecrease ∧ UnaryHistory boundary ∧ UnaryHistory routes ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont list parts sum ∧
            Cont sum weakDecrease boundary ∧ Cont boundary routes provenance ∧
              PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.PartitionUp
