import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RiemannHilbertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem RiemannHilbertBHistBridgePacket_regular_holonomic_soundness
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularClassifier deRhamReadback localSystem gluing
      transport provenance soundness endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularClassifier
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
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
    packet.right.right.right.right.right.left
  have deRhamUnary : UnaryHistory deRhamReadback :=
    unary_cont_closed derivedUnary sheafUnary deRhamCont
  have soundnessUnary : UnaryHistory soundness :=
    unary_cont_closed regularUnary deRhamUnary soundnessCont
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  exact
    And.intro soundnessUnary
      (And.intro soundnessCont
        (And.intro deRhamCont (And.intro gluingCont pkgSig)))

theorem RiemannHilbertBHistBridgePacket_local_system_ledger [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
      Cont localSystem endpoint consumer ->
        UnaryHistory gluing ∧ UnaryHistory transport ∧ UnaryHistory endpoint ∧
          UnaryHistory consumer ∧
          hsame gluing (append deRhamReadback localSystem) ∧
            hsame transport (append regularBranch gluing) ∧
              hsame endpoint (append transport provenance) ∧
                hsame consumer (append localSystem endpoint) ∧ PkgSig bundle endpoint pkg := by
  intro packet consumerRow
  have localSystemUnary : UnaryHistory localSystem :=
    packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.left
  have gluingRow : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.right.left
  have transportRow : Cont regularBranch gluing transport :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have gluingUnary : UnaryHistory gluing :=
    unary_cont_closed
      (unary_cont_closed packet.left packet.right.left packet.right.right.right.right.right.left)
      localSystemUnary gluingRow
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed packet.right.right.left gluingUnary transportRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary provenanceUnary endpointRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed localSystemUnary endpointUnary consumerRow
  exact
    ⟨gluingUnary,
      transportUnary,
      endpointUnary,
      consumerUnary,
      gluingRow,
      transportRow,
      endpointRow,
      consumerRow,
      packet.right.right.right.right.right.right.right.right.right⟩

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

theorem RiemannHilbertBHistBridgePacket_flat_connection_classifier_boundary
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint localClassifier flatSurface tail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
      hsame regularBranch (BHist.e1 tail) ->
        Cont regularBranch localSystem localClassifier ->
          Cont localClassifier deRhamReadback flatSurface ->
            UnaryHistory flatSurface ∧ (hsame flatSurface BHist.Empty -> False) ∧
              PkgSig bundle endpoint pkg := by
  intro packet regularBranchVisible localClassifierCont flatSurfaceCont
  have regularUnary : UnaryHistory regularBranch := packet.right.right.left
  have derivedUnary : UnaryHistory derivedSource := packet.left
  have sheafUnary : UnaryHistory sheafTarget := packet.right.left
  have localSystemUnary : UnaryHistory localSystem := packet.right.right.right.left
  have deRhamCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.right.left
  have deRhamUnary : UnaryHistory deRhamReadback :=
    unary_cont_closed derivedUnary sheafUnary deRhamCont
  have localClassifierUnary : UnaryHistory localClassifier :=
    unary_cont_closed regularUnary localSystemUnary localClassifierCont
  have flatSurfaceUnary : UnaryHistory flatSurface :=
    unary_cont_closed localClassifierUnary deRhamUnary flatSurfaceCont
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  constructor
  · exact flatSurfaceUnary
  · constructor
    · intro flatSurfaceEmpty
      have localClassifierNonempty : hsame localClassifier BHist.Empty -> False := by
        intro localClassifierEmpty
        have regularBranchEmpty : hsame regularBranch BHist.Empty :=
          append_eq_empty_iff.mp (localClassifierCont.symm.trans localClassifierEmpty) |>.left
        exact not_hsame_e1_empty
          (hsame_trans (hsame_symm regularBranchVisible) regularBranchEmpty)
      have localClassifierEmpty : hsame localClassifier BHist.Empty :=
        append_eq_empty_iff.mp (flatSurfaceCont.symm.trans flatSurfaceEmpty) |>.left
      exact localClassifierNonempty localClassifierEmpty
    · exact pkgSig

theorem RiemannHilbertBHistBridgePacket_de_rham_readback_scope
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
      Cont deRhamReadback regularBranch readback ->
        SemanticNameCert
            (fun row : BHist =>
              UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint))
            (fun row : BHist =>
              UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint))
            (fun row : BHist =>
              UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint))
            (fun row other : BHist =>
              (UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint)) ∧
                (UnaryHistory other ∧ (hsame other readback ∨ hsame other endpoint)) ∧
                  hsame row other) ∧
          hsame endpoint
            (append
              (append regularBranch (append (append derivedSource sheafTarget) localSystem))
              provenance) ∧
            PkgSig bundle endpoint pkg := by
  intro packet readbackCont
  have derivedUnary : UnaryHistory derivedSource := packet.left
  have sheafUnary : UnaryHistory sheafTarget := packet.right.left
  have regularUnary : UnaryHistory regularBranch := packet.right.right.left
  have deRhamCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.right.left
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.right.left
  have transportCont : Cont regularBranch gluing transport :=
    packet.right.right.right.right.right.right.right.left
  have endpointCont : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have deRhamUnary : UnaryHistory deRhamReadback :=
    unary_cont_closed derivedUnary sheafUnary deRhamCont
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed deRhamUnary regularUnary readbackCont
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint))
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint))
        (fun row : BHist =>
          UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint))
        (fun row other : BHist =>
          (UnaryHistory row ∧ (hsame row readback ∨ hsame row endpoint)) ∧
            (UnaryHistory other ∧ (hsame other readback ∨ hsame other endpoint)) ∧
              hsame row other) := by
    constructor
    · constructor
      · exact Exists.intro readback ⟨readbackUnary, Or.inl (hsame_refl readback)⟩
      · intro row carrier
        exact ⟨carrier, carrier, hsame_refl row⟩
      · intro row other classified
        exact ⟨classified.right.left, classified.left, hsame_symm classified.right.right⟩
      · intro row other third leftClass rightClass
        exact
          ⟨leftClass.left, rightClass.right.left,
            hsame_trans leftClass.right.right rightClass.right.right⟩
      · intro row other classified _carrier
        exact classified.right.left
    · intro _row source
      exact source
    · intro _row source
      exact source
  have endpointSame :
      hsame endpoint
        (append
          (append regularBranch (append (append derivedSource sheafTarget) localSystem))
          provenance) := by
    cases deRhamCont
    cases gluingCont
    cases transportCont
    cases endpointCont
    rfl
  exact ⟨semantic, endpointSame, pkgSig⟩

theorem RiemannHilbertBHistBridgePacket_deRham_readback_scope
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing
      transport provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
      UnaryHistory derivedSource ∧ UnaryHistory sheafTarget ∧
        UnaryHistory regularBranch ∧ UnaryHistory deRhamReadback ∧
          UnaryHistory localSystem ∧ UnaryHistory gluing ∧
            hsame deRhamReadback (append derivedSource sheafTarget) ∧
              hsame gluing (append (append derivedSource sheafTarget) localSystem) ∧
                hsame endpoint
                    (append
                      (append regularBranch
                        (append (append derivedSource sheafTarget) localSystem))
                      provenance) ∧
                  PkgSig bundle endpoint pkg := by
  intro packet
  have derivedUnary : UnaryHistory derivedSource := packet.left
  have sheafUnary : UnaryHistory sheafTarget := packet.right.left
  have regularUnary : UnaryHistory regularBranch := packet.right.right.left
  have localUnary : UnaryHistory localSystem := packet.right.right.right.left
  have deRhamCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.right.left
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.right.left
  have transportCont : Cont regularBranch gluing transport :=
    packet.right.right.right.right.right.right.right.left
  have endpointCont : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have deRhamUnary : UnaryHistory deRhamReadback :=
    unary_cont_closed derivedUnary sheafUnary deRhamCont
  have gluingUnary : UnaryHistory gluing :=
    unary_cont_closed deRhamUnary localUnary gluingCont
  cases deRhamCont
  cases gluingCont
  cases transportCont
  cases endpointCont
  exact
    And.intro derivedUnary
      (And.intro sheafUnary
        (And.intro regularUnary
          (And.intro deRhamUnary
            (And.intro localUnary
              (And.intro gluingUnary
                (And.intro rfl
                  (And.intro rfl
                    (And.intro rfl pkgSig))))))))

theorem RiemannHilbertBHistBridgePacket_de_Rham_readback_scope
    [AskSetup] [PackageSetup]
    {derivedSource sheafTarget regularBranch deRhamReadback localSystem gluing transport
      provenance endpoint readbackScope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannHilbertBHistBridgePacket derivedSource sheafTarget regularBranch
        deRhamReadback localSystem gluing transport provenance endpoint bundle pkg ->
      Cont endpoint deRhamReadback readbackScope ->
        UnaryHistory readbackScope ∧ hsame readbackScope (append endpoint deRhamReadback) ∧
          Cont derivedSource sheafTarget deRhamReadback ∧
            Cont deRhamReadback localSystem gluing ∧
              Cont regularBranch gluing transport ∧
                Cont transport provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet readbackCont
  have derivedUnary : UnaryHistory derivedSource := packet.left
  have sheafUnary : UnaryHistory sheafTarget := packet.right.left
  have regularUnary : UnaryHistory regularBranch := packet.right.right.left
  have deRhamCont : Cont derivedSource sheafTarget deRhamReadback :=
    packet.right.right.right.right.right.left
  have gluingCont : Cont deRhamReadback localSystem gluing :=
    packet.right.right.right.right.right.right.left
  have transportCont : Cont regularBranch gluing transport :=
    packet.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.left
  have endpointCont : Cont transport provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have deRhamUnary : UnaryHistory deRhamReadback :=
    unary_cont_closed derivedUnary sheafUnary deRhamCont
  have localSystemUnary : UnaryHistory localSystem :=
    packet.right.right.right.left
  have gluingUnary : UnaryHistory gluing :=
    unary_cont_closed deRhamUnary localSystemUnary gluingCont
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed regularUnary gluingUnary transportCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary provenanceUnary endpointCont
  have readbackUnary : UnaryHistory readbackScope :=
    unary_cont_closed endpointUnary deRhamUnary readbackCont
  exact
    And.intro readbackUnary
      (And.intro readbackCont
        (And.intro deRhamCont
          (And.intro gluingCont
            (And.intro transportCont (And.intro endpointCont pkgSig)))))

end BEDC.Derived.RiemannHilbertUp
