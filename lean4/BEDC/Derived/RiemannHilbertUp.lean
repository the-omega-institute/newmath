import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RiemannHilbertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RiemannHilbertBHistBridgePacket [AskSetup] [PackageSetup]
    (derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧ UnaryHistory regularBranch ∧
    UnaryHistory localSystem ∧ Cont derivedSource sheafTarget deRhamReadback ∧
      Cont deRhamReadback localSystem gluing ∧ Cont gluing regularBranch endpoint ∧
        PkgSig bundle endpoint pkg

theorem RiemannHilbertBHistBridgePacket_derived_sheaf_source
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing endpoint bundle pkg ->
      UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧
        Cont derivedSource sheafTarget deRhamReadback ∧
          Cont deRhamReadback localSystem gluing ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact
    ⟨packet.left,
      packet.right.left,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right⟩

theorem RiemannHilbertBHistBridgePacket_source_boundary [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing endpoint bundle pkg ->
      UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧
        hsame deRhamReadback (append derivedSource sheafTarget) ∧
          hsame endpoint
              (append (append (append derivedSource sheafTarget) localSystem)
                regularBranch) ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have derivedSourceUnary : UnaryHistory derivedSource := packet.left
  have sheafTargetUnary : UnaryHistory sheafTarget := packet.right.left
  have deRhamReadbackCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.left
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.left
  have endpointCont : Cont gluing regularBranch endpoint :=
    packet.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right
  cases deRhamReadbackCont
  cases gluingCont
  cases endpointCont
  exact
    ⟨derivedSourceUnary,
      sheafTargetUnary,
      rfl,
      rfl,
      pkgSig⟩

theorem RiemannHilbertBHistBridgePacket_regular_holonomic_soundness
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularClassifier deRhamReadback localSystem gluing
      soundness endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularClassifier
        deRhamReadback localSystem gluing endpoint bundle pkg ->
      Cont regularClassifier deRhamReadback soundness ->
        UnaryHistory soundness ∧ hsame soundness (append regularClassifier deRhamReadback) ∧
          Cont derivedSource sheafTarget deRhamReadback ∧
            Cont deRhamReadback localSystem gluing ∧ PkgSig bundle endpoint pkg := by
  intro packet soundnessCont
  have regularUnary : UnaryHistory regularClassifier :=
    packet.right.right.left
  have derivedUnary : UnaryHistory derivedSource := packet.left
  have sheafUnary : UnaryHistory sheafTarget := packet.right.left
  have deRhamCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.left
  have deRhamUnary : UnaryHistory deRhamReadback :=
    unary_cont_closed derivedUnary sheafUnary deRhamCont
  have soundnessUnary : UnaryHistory soundness :=
    unary_cont_closed regularUnary deRhamUnary soundnessCont
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right
  exact
    And.intro soundnessUnary
      (And.intro soundnessCont
        (And.intro deRhamCont (And.intro gluingCont pkgSig)))

theorem RiemannHilbertBridgePacket_derived_sheaf_source_rows [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularHolonomic transport provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory derivedSource ->
      UnaryHistory sheafTarget ->
        UnaryHistory regularHolonomic ->
          UnaryHistory provenance ->
            Cont derivedSource sheafTarget transport ->
              Cont transport provenance endpoint ->
                PkgSig bundle endpoint pkg ->
                  UnaryHistory transport ∧
                    UnaryHistory endpoint ∧
                      hsame transport (append derivedSource sheafTarget) ∧
                        hsame endpoint (append transport provenance) ∧ PkgSig bundle endpoint pkg := by
  intro derivedUnary sheafUnary _ provenanceUnary transportCont endpointCont pkgSig
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed derivedUnary sheafUnary transportCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary provenanceUnary endpointCont
  cases transportCont
  cases endpointCont
  exact
    ⟨transportUnary,
      endpointUnary,
      rfl,
      rfl,
      pkgSig⟩

end BEDC.Derived.RiemannHilbertUp
