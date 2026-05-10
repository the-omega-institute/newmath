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

theorem RiemannHilbertDerivedSheafSource_composite_boundary
    {derived sheaf regular deRham localRow transport sourceTarget localLedger publicBoundary :
      BHist} :
    Cont derived sheaf sourceTarget -> Cont regular deRham transport ->
      Cont localRow transport localLedger -> Cont sourceTarget localLedger publicBoundary ->
        UnaryHistory derived -> UnaryHistory sheaf -> UnaryHistory regular ->
          UnaryHistory deRham -> UnaryHistory localRow ->
            UnaryHistory sourceTarget ∧ UnaryHistory transport ∧ UnaryHistory localLedger ∧
              UnaryHistory publicBoundary ∧
                hsame publicBoundary
                  (append (append derived sheaf) (append localRow (append regular deRham))) := by
  intro sourceRoute transportRoute localRoute boundaryRoute derivedUnary sheafUnary regularUnary
    deRhamUnary localUnary
  have sourceUnary : UnaryHistory sourceTarget :=
    unary_cont_closed derivedUnary sheafUnary sourceRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed regularUnary deRhamUnary transportRoute
  have localLedgerUnary : UnaryHistory localLedger :=
    unary_cont_closed localUnary transportUnary localRoute
  have boundaryUnary : UnaryHistory publicBoundary :=
    unary_cont_closed sourceUnary localLedgerUnary boundaryRoute
  have boundaryReadback :
      hsame publicBoundary
        (append (append derived sheaf) (append localRow (append regular deRham))) := by
    cases sourceRoute
    cases transportRoute
    cases localRoute
    cases boundaryRoute
    rfl
  exact
    ⟨sourceUnary, transportUnary, localLedgerUnary, boundaryUnary, boundaryReadback⟩

theorem RiemannHilbertLocalSystemLedger_continuation_closure
    {sheaf horizontal localRow deRham localSystem derived compare provenance ledger : BHist} :
    Cont sheaf horizontal localRow -> Cont localRow deRham localSystem ->
      Cont derived localSystem compare -> Cont compare provenance ledger ->
        UnaryHistory sheaf -> UnaryHistory horizontal -> UnaryHistory deRham ->
          UnaryHistory derived -> UnaryHistory provenance ->
            UnaryHistory localRow ∧ UnaryHistory localSystem ∧ UnaryHistory compare ∧
              UnaryHistory ledger ∧
                hsame ledger
                  (append (append derived (append (append sheaf horizontal) deRham))
                    provenance) := by
  intro localRoute localSystemRoute compareRoute ledgerRoute sheafUnary horizontalUnary
    deRhamUnary derivedUnary provenanceUnary
  have localUnary : UnaryHistory localRow :=
    unary_cont_closed sheafUnary horizontalUnary localRoute
  have localSystemUnary : UnaryHistory localSystem :=
    unary_cont_closed localUnary deRhamUnary localSystemRoute
  have compareUnary : UnaryHistory compare :=
    unary_cont_closed derivedUnary localSystemUnary compareRoute
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed compareUnary provenanceUnary ledgerRoute
  have ledgerReadback :
      hsame ledger
        (append (append derived (append (append sheaf horizontal) deRham)) provenance) := by
    cases localRoute
    cases localSystemRoute
    cases compareRoute
    cases ledgerRoute
    rfl
  exact ⟨localUnary, localSystemUnary, compareUnary, ledgerUnary, ledgerReadback⟩

end BEDC.Derived.RiemannHilbertUp
