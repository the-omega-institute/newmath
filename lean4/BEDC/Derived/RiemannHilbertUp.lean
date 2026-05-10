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
    (derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧ UnaryHistory regularBranch ∧
    UnaryHistory localSystem ∧ UnaryHistory provenance ∧
      Cont derivedSource sheafTarget deRhamReadback ∧
        Cont deRhamReadback localSystem gluing ∧ Cont regularBranch gluing transport ∧
          Cont transport provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem RiemannHilbertBHistBridgePacket_derived_sheaf_source
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
      UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧
        Cont derivedSource sheafTarget deRhamReadback ∧
          Cont deRhamReadback localSystem gluing ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact
    ⟨packet.left,
      packet.right.left,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right⟩

theorem RiemannHilbertBHistBridgePacket_source_boundary [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
      UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧
        hsame deRhamReadback (append derivedSource sheafTarget) ∧
          hsame endpoint
              (append
                (append regularBranch (append (append derivedSource sheafTarget) localSystem))
                provenance) ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have derivedSourceUnary : UnaryHistory derivedSource := packet.left
  have sheafTargetUnary : UnaryHistory sheafTarget := packet.right.left
  have deRhamReadbackCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.right.left
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.right.left
  have transportCont : Cont regularBranch gluing transport :=
    packet.right.right.right.right.right.right.right.left
  have endpointCont : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  cases deRhamReadbackCont
  cases gluingCont
  cases transportCont
  cases endpointCont
  exact
    ⟨derivedSourceUnary,
      sheafTargetUnary,
      rfl,
      rfl,
      pkgSig⟩

theorem RiemannHilbertBHistBridgePacket_flat_connection_classifier
    [AskSetup] [PackageSetup]
    {derived sheaf regularHolonomic deRham localSystem gluing transport provenance endpoint
      derived' sheaf' regularHolonomic' deRham' localSystem' gluing' transport'
      provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derived sheaf regularHolonomic deRham localSystem
        gluing transport provenance endpoint bundle pkg ->
      hsame derived derived' ->
      hsame sheaf sheaf' ->
      hsame regularHolonomic regularHolonomic' ->
      hsame localSystem localSystem' ->
      hsame provenance provenance' ->
      Cont derived' sheaf' deRham' ->
      Cont deRham' localSystem' gluing' ->
      Cont regularHolonomic' gluing' transport' ->
      Cont transport' provenance' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      RiemannHilbertBHistBridgePacket derived' sheaf' regularHolonomic' deRham'
          localSystem' gluing' transport' provenance' endpoint' bundle pkg ∧
        hsame deRham deRham' ∧ hsame gluing gluing' ∧ hsame transport transport' ∧
          hsame endpoint endpoint' := by
  intro packet sameDerived sameSheaf sameRegularHolonomic sameLocalSystem sameProvenance
    deRhamCont' gluingCont' transportCont' endpointCont' pkgSig'
  have sameDeRham : hsame deRham deRham' :=
    cont_respects_hsame sameDerived sameSheaf
      packet.right.right.right.right.right.left deRhamCont'
  have sameGluing : hsame gluing gluing' :=
    cont_respects_hsame sameDeRham sameLocalSystem
      packet.right.right.right.right.right.right.left gluingCont'
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameRegularHolonomic sameGluing
      packet.right.right.right.right.right.right.right.left transportCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameTransport sameProvenance
      packet.right.right.right.right.right.right.right.right.left endpointCont'
  exact
    ⟨⟨unary_transport packet.left sameDerived,
        unary_transport packet.right.left sameSheaf,
        unary_transport packet.right.right.left sameRegularHolonomic,
        unary_transport packet.right.right.right.left sameLocalSystem,
        unary_transport packet.right.right.right.right.left sameProvenance,
        deRhamCont', gluingCont', transportCont', endpointCont', pkgSig'⟩,
      sameDeRham, sameGluing, sameTransport, sameEndpoint⟩

end BEDC.Derived.RiemannHilbertUp
