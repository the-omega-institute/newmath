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

def RiemannHilbertBHistBridgePacket [AskSetup] [PackageSetup]
    (derivedSource sheafTarget regularClassifier deRhamReadback localSystem gluing
      derivedToSheaf localRead gluingRead endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧ UnaryHistory regularClassifier ∧
    UnaryHistory deRhamReadback ∧ UnaryHistory localSystem ∧ UnaryHistory gluing ∧
      Cont derivedSource sheafTarget derivedToSheaf ∧
        Cont deRhamReadback localSystem localRead ∧
          Cont localSystem gluing gluingRead ∧
            Cont derivedToSheaf gluingRead endpoint ∧
              PkgSig bundle endpoint pkg

theorem RiemannHilbertBHistBridgePacket_regular_holonomic_soundness
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularClassifier deRhamReadback localSystem gluing
      derivedToSheaf localRead gluingRead soundness endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularClassifier
        deRhamReadback localSystem gluing derivedToSheaf localRead gluingRead endpoint
        bundle pkg ->
      Cont regularClassifier deRhamReadback soundness ->
        UnaryHistory soundness ∧ hsame soundness (append regularClassifier deRhamReadback) ∧
          Cont derivedSource sheafTarget derivedToSheaf ∧
            Cont localSystem gluing gluingRead ∧ PkgSig bundle endpoint pkg := by
  intro packet soundnessCont
  have regularUnary : UnaryHistory regularClassifier :=
    packet.right.right.left
  have deRhamUnary : UnaryHistory deRhamReadback :=
    packet.right.right.right.left
  have soundnessUnary : UnaryHistory soundness :=
    unary_cont_closed regularUnary deRhamUnary soundnessCont
  have derivedToSheafCont : Cont derivedSource sheafTarget derivedToSheaf :=
    packet.right.right.right.right.right.right.left
  have gluingReadCont : Cont localSystem gluing gluingRead :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  exact
    And.intro soundnessUnary
      (And.intro soundnessCont
        (And.intro derivedToSheafCont (And.intro gluingReadCont pkgSig)))

end BEDC.Derived.RiemannHilbertUp
