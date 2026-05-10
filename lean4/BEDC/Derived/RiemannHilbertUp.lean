import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RiemannHilbertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RiemannHilbertBHistBridgePacket [AskSetup] [PackageSetup]
    (derived sheaf regular deRham localSystem gluing provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derived ∧ UnaryHistory sheaf ∧ UnaryHistory regular ∧
    Cont derived sheaf deRham ∧ Cont localSystem gluing endpoint ∧
      Cont regular deRham provenance ∧ PkgSig bundle endpoint pkg

theorem RiemannHilbertBHistBridgePacket_derived_sheaf_source
    [AskSetup] [PackageSetup]
    {derived sheaf regular deRham localSystem gluing provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derived sheaf regular deRham localSystem gluing
        provenance endpoint bundle pkg ->
      UnaryHistory derived ∧ UnaryHistory sheaf ∧ Cont derived sheaf deRham ∧
        Cont localSystem gluing endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.right.left
        (And.intro packet.right.right.right.right.left
          packet.right.right.right.right.right.right)))

end BEDC.Derived.RiemannHilbertUp
