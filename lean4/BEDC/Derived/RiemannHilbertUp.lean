import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RiemannHilbertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RiemannHilbertBridgePacket [AskSetup] [PackageSetup]
    (derived sheaf regular deRham localSystem gluing sourceBridge targetBridge endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derived ∧ UnaryHistory sheaf ∧ UnaryHistory regular ∧ UnaryHistory deRham ∧
    UnaryHistory localSystem ∧ UnaryHistory gluing ∧ Cont derived sheaf sourceBridge ∧
      Cont regular deRham targetBridge ∧ Cont sourceBridge targetBridge endpoint ∧
        PkgSig bundle endpoint pkg

theorem RiemannHilbertBridgePacket_derived_sheaf_source [AskSetup] [PackageSetup]
    {derived sheaf regular deRham localSystem gluing sourceBridge targetBridge endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBridgePacket derived sheaf regular deRham localSystem gluing sourceBridge
        targetBridge endpoint bundle pkg ->
      UnaryHistory sourceBridge ∧ UnaryHistory targetBridge ∧ UnaryHistory endpoint ∧
        hsame sourceBridge (append derived sheaf) ∧
          hsame targetBridge (append regular deRham) ∧
            hsame endpoint (append sourceBridge targetBridge) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have sourceUnary : UnaryHistory sourceBridge :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.right.right.left
  have targetUnary : UnaryHistory targetBridge :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sourceUnary targetUnary packet.right.right.right.right.right.right.right.right.left
  exact And.intro sourceUnary
    (And.intro targetUnary
      (And.intro endpointUnary
        (And.intro packet.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right.right.right)))))

end BEDC.Derived.RiemannHilbertUp
