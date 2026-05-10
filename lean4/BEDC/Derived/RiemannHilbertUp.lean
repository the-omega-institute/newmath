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

theorem RiemannHilbertBHistBridgePacket_sheaf_gluing_exactness [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing gluing'
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
      deRhamReadback localSystem gluing endpoint bundle pkg ->
      hsame gluing gluing' -> Cont gluing' regularBranch endpoint' ->
        RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
          deRhamReadback localSystem gluing' endpoint' bundle pkg ∧ hsame endpoint endpoint' := by
  intro packet sameGluing glued
  have localGluing : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.left
  have originalEndpoint : Cont gluing regularBranch endpoint :=
    packet.right.right.right.right.right.right.left
  have transportedLocalGluing : Cont deRhamReadback localSystem gluing' :=
    cont_result_hsame_transport localGluing sameGluing
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameGluing (hsame_refl regularBranch) originalEndpoint glued
  cases sameEndpoint
  constructor
  · exact
      ⟨packet.left,
        packet.right.left,
        packet.right.right.left,
        packet.right.right.right.left,
        packet.right.right.right.right.left,
        transportedLocalGluing,
        glued,
        packet.right.right.right.right.right.right.right⟩
  · exact hsame_refl endpoint

end BEDC.Derived.RiemannHilbertUp
