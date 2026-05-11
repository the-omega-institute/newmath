import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.Commutativity

namespace BEDC.Derived.HolonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HolonomyTransportCarrier [AskSetup] [PackageSetup]
    (bundle connection loop endpoint curvature ledger provenance : BHist)
    (probeBundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundle ∧ UnaryHistory connection ∧ UnaryHistory loop ∧
    UnaryHistory endpoint ∧ UnaryHistory curvature ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont loop connection ledger ∧ Cont ledger curvature endpoint ∧
        PkgSig probeBundle endpoint pkg

theorem HolonomyTransportCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvature ledger provenance : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
        probeBundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
            probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
            probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
            probeBundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem HolonomyTransportCarrier_curvature_loop_boundary [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvature ledger provenance : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
        probeBundle pkg ->
      UnaryHistory loop ∧ UnaryHistory curvature ∧ UnaryHistory ledger ∧
        Cont loop connection ledger ∧ Cont ledger curvature endpoint ∧
          PkgSig probeBundle endpoint pkg := by
  intro carrier
  rcases carrier with
    ⟨_bundleUnary, _connectionUnary, loopUnary, _endpointUnary, curvatureUnary, ledgerUnary,
      _provenanceUnary, loopConnectionLedger, ledgerCurvatureEndpoint, endpointPkg⟩
  exact
    ⟨loopUnary, curvatureUnary, ledgerUnary, loopConnectionLedger, ledgerCurvatureEndpoint,
      endpointPkg⟩

def HolonomyBHistTransportCarrier [AskSetup] [PackageSetup]
    (bundleRow connectionRow loopRow endpointRow curvatureRow controlRow ledgerRow
      dependencyRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundleRow ∧ UnaryHistory connectionRow ∧ UnaryHistory endpointRow ∧
    UnaryHistory curvatureRow ∧ UnaryHistory controlRow ∧ UnaryHistory loopRow ∧
      UnaryHistory ledgerRow ∧ UnaryHistory dependencyRow ∧
        Cont bundleRow connectionRow loopRow ∧ Cont loopRow endpointRow ledgerRow ∧
          Cont curvatureRow controlRow dependencyRow ∧ PkgSig bundle dependencyRow pkg

theorem HolonomyBHistTransportCarrier_continuation_transport_stability [AskSetup]
    [PackageSetup]
    {bundleRow connectionRow loopRow endpointRow curvatureRow controlRow ledgerRow
      dependencyRow bundleRow' connectionRow' loopRow' endpointRow' curvatureRow'
      controlRow' ledgerRow' dependencyRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyBHistTransportCarrier bundleRow connectionRow loopRow endpointRow curvatureRow
        controlRow ledgerRow dependencyRow bundle pkg ->
      hsame bundleRow bundleRow' ->
        hsame connectionRow connectionRow' ->
          hsame endpointRow endpointRow' ->
            hsame curvatureRow curvatureRow' ->
              hsame controlRow controlRow' ->
                Cont bundleRow' connectionRow' loopRow' ->
                  Cont loopRow' endpointRow' ledgerRow' ->
                    Cont curvatureRow' controlRow' dependencyRow' ->
                      PkgSig bundle dependencyRow' pkg ->
                        HolonomyBHistTransportCarrier bundleRow' connectionRow' loopRow'
                            endpointRow' curvatureRow' controlRow' ledgerRow' dependencyRow'
                            bundle pkg ∧
                          hsame loopRow loopRow' ∧ hsame ledgerRow ledgerRow' ∧
                            hsame dependencyRow dependencyRow' := by
  intro carrier sameBundle sameConnection sameEndpoint sameCurvature sameControl
    loopRow'Cont ledgerRow'Cont dependencyRow'Cont pkg'
  have bundleUnary' : UnaryHistory bundleRow' :=
    unary_transport carrier.left sameBundle
  have connectionUnary' : UnaryHistory connectionRow' :=
    unary_transport carrier.right.left sameConnection
  have endpointUnary' : UnaryHistory endpointRow' :=
    unary_transport carrier.right.right.left sameEndpoint
  have curvatureUnary' : UnaryHistory curvatureRow' :=
    unary_transport carrier.right.right.right.left sameCurvature
  have controlUnary' : UnaryHistory controlRow' :=
    unary_transport carrier.right.right.right.right.left sameControl
  have sameLoop : hsame loopRow loopRow' :=
    cont_respects_hsame sameBundle sameConnection
      carrier.right.right.right.right.right.right.right.right.left loopRow'Cont
  have loopUnary' : UnaryHistory loopRow' :=
    unary_cont_closed bundleUnary' connectionUnary' loopRow'Cont
  have sameLedger : hsame ledgerRow ledgerRow' :=
    cont_respects_hsame sameLoop sameEndpoint
      carrier.right.right.right.right.right.right.right.right.right.left ledgerRow'Cont
  have ledgerUnary' : UnaryHistory ledgerRow' :=
    unary_cont_closed loopUnary' endpointUnary' ledgerRow'Cont
  have sameDependency : hsame dependencyRow dependencyRow' :=
    cont_respects_hsame sameCurvature sameControl
      carrier.right.right.right.right.right.right.right.right.right.right.left
      dependencyRow'Cont
  have dependencyUnary' : UnaryHistory dependencyRow' :=
    unary_cont_closed curvatureUnary' controlUnary' dependencyRow'Cont
  exact
    And.intro
      (And.intro bundleUnary'
        (And.intro connectionUnary'
          (And.intro endpointUnary'
            (And.intro curvatureUnary'
              (And.intro controlUnary'
                (And.intro loopUnary'
                  (And.intro ledgerUnary'
                    (And.intro dependencyUnary'
                      (And.intro loopRow'Cont
                        (And.intro ledgerRow'Cont
                          (And.intro dependencyRow'Cont pkg')))))))))))
      (And.intro sameLoop (And.intro sameLedger sameDependency))

def HolonomyTransportPacket [AskSetup] [PackageSetup]
    (bundle connection loop endpoint curvatureLedger compositionLedger provenance : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory bundle ∧ UnaryHistory connection ∧ UnaryHistory loop ∧
    UnaryHistory endpoint ∧ UnaryHistory curvatureLedger ∧
      UnaryHistory compositionLedger ∧ UnaryHistory provenance ∧
        Cont connection loop endpoint ∧ Cont endpoint curvatureLedger compositionLedger ∧
          PkgSig probe provenance pkg

theorem HolonomyTransportPacket_parallel_transport_stability [AskSetup] [PackageSetup]
    {bundle bundle' connection connection' loop loop' endpoint endpoint' curvatureLedger
      curvatureLedger' compositionLedger compositionLedger' provenance provenance' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvatureLedger compositionLedger
        provenance probe pkg ->
      hsame bundle bundle' -> hsame connection connection' -> hsame loop loop' ->
        hsame endpoint endpoint' -> hsame curvatureLedger curvatureLedger' ->
          hsame compositionLedger compositionLedger' -> hsame provenance provenance' ->
            PkgSig probe provenance' pkg ->
              HolonomyTransportPacket bundle' connection' loop' endpoint' curvatureLedger'
                  compositionLedger' provenance' probe pkg ∧
                hsame endpoint endpoint' := by
  intro packet sameBundle sameConnection sameLoop sameEndpoint sameCurvatureLedger
    sameCompositionLedger sameProvenance pkgSig'
  have bundleUnary' : UnaryHistory bundle' :=
    unary_transport packet.left sameBundle
  have connectionUnary' : UnaryHistory connection' :=
    unary_transport packet.right.left sameConnection
  have loopUnary' : UnaryHistory loop' :=
    unary_transport packet.right.right.left sameLoop
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport packet.right.right.right.left sameEndpoint
  have curvatureLedgerUnary' : UnaryHistory curvatureLedger' :=
    unary_transport packet.right.right.right.right.left sameCurvatureLedger
  have compositionLedgerUnary' : UnaryHistory compositionLedger' :=
    unary_transport packet.right.right.right.right.right.left sameCompositionLedger
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have endpointRow' : Cont connection' loop' endpoint' :=
    cont_hsame_transport sameConnection sameLoop sameEndpoint
      packet.right.right.right.right.right.right.right.left
  have compositionRow' : Cont endpoint' curvatureLedger' compositionLedger' :=
    cont_hsame_transport sameEndpoint sameCurvatureLedger sameCompositionLedger
      packet.right.right.right.right.right.right.right.right.left
  exact
    And.intro
      (And.intro bundleUnary'
        (And.intro connectionUnary'
          (And.intro loopUnary'
            (And.intro endpointUnary'
              (And.intro curvatureLedgerUnary'
                (And.intro compositionLedgerUnary'
                  (And.intro provenanceUnary'
                    (And.intro endpointRow'
                      (And.intro compositionRow' pkgSig')))))))))
      sameEndpoint

theorem HolonomyTransportPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvatureLedger compositionLedger provenance : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvatureLedger compositionLedger
        provenance probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          hsame ∧
        Cont connection loop endpoint ∧ Cont endpoint curvatureLedger compositionLedger ∧
          PkgSig probe provenance pkg := by
  intro packet
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
            provenance probe pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | intro e endpointWitness =>
            exact Exists.intro e
              (And.intro endpointWitness.left
                (hsame_trans (hsame_symm sameRows) endpointWitness.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.right.right.right.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.right.right.right.left
        packet.right.right.right.right.right.right.right.right.right))

theorem HolonomyTransportPacket_certificate_boundary [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvatureLedger compositionLedger provenance : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvatureLedger compositionLedger
        provenance probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          hsame ∧
        UnaryHistory bundle ∧ UnaryHistory connection ∧ UnaryHistory loop ∧
          UnaryHistory endpoint ∧ UnaryHistory curvatureLedger ∧
            UnaryHistory compositionLedger ∧ UnaryHistory provenance ∧
              Cont connection loop endpoint ∧ Cont endpoint curvatureLedger compositionLedger ∧
                PkgSig probe provenance pkg := by
  intro packet
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
            provenance probe pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              HolonomyTransportPacket bundle connection loop e curvatureLedger compositionLedger
                provenance probe pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | intro e endpointWitness =>
            exact Exists.intro e
              (And.intro endpointWitness.left
                (hsame_trans (hsame_symm sameRows) endpointWitness.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.left
                  (And.intro packet.right.right.right.right.right.right.right.left
                    (And.intro packet.right.right.right.right.right.right.right.right.left
                      packet.right.right.right.right.right.right.right.right.right)))))))))

theorem HolonomyTransportPacket_curvature_loop_boundary [AskSetup] [PackageSetup]
    {bundle connection loop endpoint endpoint' curvatureLedger curvatureLedger'
      compositionLedger compositionLedger' provenance provenance' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvatureLedger compositionLedger
        provenance probe pkg ->
      hsame endpoint endpoint' ->
        hsame curvatureLedger curvatureLedger' ->
          hsame provenance provenance' ->
            Cont endpoint' curvatureLedger' compositionLedger' ->
              PkgSig probe provenance' pkg ->
                HolonomyTransportPacket bundle connection loop endpoint' curvatureLedger'
                    compositionLedger' provenance' probe pkg ∧
                  hsame compositionLedger compositionLedger' := by
  intro packet sameEndpoint sameCurvatureLedger sameProvenance compositionLedgerRow'
    pkgSig'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport packet.right.right.right.left sameEndpoint
  have curvatureLedgerUnary' : UnaryHistory curvatureLedger' :=
    unary_transport packet.right.right.right.right.left sameCurvatureLedger
  have compositionLedgerUnary' : UnaryHistory compositionLedger' :=
    unary_cont_closed endpointUnary' curvatureLedgerUnary' compositionLedgerRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have endpointRow' : Cont connection loop endpoint' :=
    cont_result_hsame_transport packet.right.right.right.right.right.right.right.left
      sameEndpoint
  have sameCompositionLedger : hsame compositionLedger compositionLedger' :=
    cont_respects_hsame sameEndpoint sameCurvatureLedger
      packet.right.right.right.right.right.right.right.right.left compositionLedgerRow'
  exact
    And.intro
      (And.intro packet.left
        (And.intro packet.right.left
          (And.intro packet.right.right.left
            (And.intro endpointUnary'
              (And.intro curvatureLedgerUnary'
                (And.intro compositionLedgerUnary'
                  (And.intro provenanceUnary'
                    (And.intro endpointRow'
                      (And.intro compositionLedgerRow' pkgSig')))))))))
      sameCompositionLedger

theorem HolonomyTransportCarrier_parallel_transport_stability [AskSetup] [PackageSetup]
    {bundle bundle' connection connection' loop loop' endpoint endpoint' curvature curvature'
      ledger ledger' provenance provenance' : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportCarrier bundle connection loop endpoint curvature ledger provenance
        probeBundle pkg ->
      hsame bundle bundle' ->
        hsame connection connection' ->
          hsame loop loop' ->
            hsame curvature curvature' ->
              hsame provenance provenance' ->
                Cont loop' connection' ledger' ->
                  Cont ledger' curvature' endpoint' ->
                    PkgSig probeBundle endpoint' pkg ->
                      HolonomyTransportCarrier bundle' connection' loop' endpoint' curvature'
                          ledger' provenance' probeBundle pkg ∧
                        hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro carrier sameBundle sameConnection sameLoop sameCurvature sameProvenance
  intro ledgerRow' endpointRow' pkgSig'
  have bundleUnary' : UnaryHistory bundle' :=
    unary_transport carrier.left sameBundle
  have connectionUnary' : UnaryHistory connection' :=
    unary_transport carrier.right.left sameConnection
  have loopUnary' : UnaryHistory loop' :=
    unary_transport carrier.right.right.left sameLoop
  have curvatureUnary' : UnaryHistory curvature' :=
    unary_transport carrier.right.right.right.right.left sameCurvature
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameLoop sameConnection
      carrier.right.right.right.right.right.right.right.left ledgerRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed loopUnary' connectionUnary' ledgerRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger sameCurvature
      carrier.right.right.right.right.right.right.right.right.left endpointRow'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed ledgerUnary' curvatureUnary' endpointRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport carrier.right.right.right.right.right.right.left sameProvenance
  exact
    And.intro
      (And.intro bundleUnary'
        (And.intro connectionUnary'
          (And.intro loopUnary'
            (And.intro endpointUnary'
              (And.intro curvatureUnary'
                (And.intro ledgerUnary'
                  (And.intro provenanceUnary'
                    (And.intro ledgerRow'
                      (And.intro endpointRow' pkgSig')))))))))
      (And.intro sameLedger sameEndpoint)

theorem HolonomyTransportCarrier_composition_ledger_obligation [AskSetup] [PackageSetup]
    {bundle connection loopA endpointA curvature ledgerA provenance loopB endpointB ledgerB
      composedLoop composedEndpoint : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportCarrier bundle connection loopA endpointA curvature ledgerA provenance
        probeBundle pkg ->
      HolonomyTransportCarrier bundle connection loopB endpointB curvature ledgerB provenance
          probeBundle pkg ->
        Cont loopA loopB composedLoop ->
          Cont ledgerA ledgerB composedEndpoint ->
            PkgSig probeBundle composedEndpoint pkg ->
              UnaryHistory composedLoop ∧ UnaryHistory composedEndpoint ∧
                hsame composedLoop (append loopA loopB) ∧
                  hsame composedEndpoint (append ledgerA ledgerB) ∧
                    Cont loopA loopB composedLoop ∧ Cont ledgerA ledgerB composedEndpoint ∧
                      PkgSig probeBundle composedEndpoint pkg := by
  intro carrierA carrierB loopComposition ledgerComposition composedPkg
  have loopAUnary : UnaryHistory loopA :=
    carrierA.right.right.left
  have loopBUnary : UnaryHistory loopB :=
    carrierB.right.right.left
  have ledgerAUnary : UnaryHistory ledgerA :=
    carrierA.right.right.right.right.right.left
  have ledgerBUnary : UnaryHistory ledgerB :=
    carrierB.right.right.right.right.right.left
  have composedLoopUnary : UnaryHistory composedLoop :=
    unary_cont_closed loopAUnary loopBUnary loopComposition
  have composedEndpointUnary : UnaryHistory composedEndpoint :=
    unary_cont_closed ledgerAUnary ledgerBUnary ledgerComposition
  exact And.intro composedLoopUnary
    (And.intro composedEndpointUnary
      (And.intro loopComposition
        (And.intro ledgerComposition
          (And.intro loopComposition (And.intro ledgerComposition composedPkg)))))

theorem HolonomyTransportPacket_loop_source_obligation [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvature ledger pkgRow : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvature ledger pkgRow probe pkg ->
      UnaryHistory bundle ∧ UnaryHistory connection ∧ UnaryHistory loop ∧
        UnaryHistory endpoint ∧ UnaryHistory ledger ∧
          hsame endpoint (append loop connection) ∧
            hsame ledger (append endpoint curvature) ∧ PkgSig probe pkgRow pkg := by
  intro packet
  have endpointFromConnection : hsame endpoint (append connection loop) :=
    packet.right.right.right.right.right.right.right.left
  have endpointFromLoop : hsame endpoint (append loop connection) :=
    hsame_trans endpointFromConnection
      (unary_append_comm_hsame packet.right.left packet.right.right.left)
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left
          (And.intro packet.right.right.right.right.right.left
             (And.intro endpointFromLoop
               (And.intro packet.right.right.right.right.right.right.right.right.left
                 packet.right.right.right.right.right.right.right.right.right))))))

theorem HolonomyTransportPacket_composition_ledger_obligation [AskSetup] [PackageSetup]
    {bundle connection loop endpoint curvatureLedger compositionLedger provenance : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    HolonomyTransportPacket bundle connection loop endpoint curvatureLedger compositionLedger
        provenance probe pkg ->
      exists loopCurvature : BHist,
        UnaryHistory loopCurvature ∧ Cont loop curvatureLedger loopCurvature ∧
          Cont connection loopCurvature compositionLedger ∧
            hsame compositionLedger (append connection loopCurvature) ∧
              PkgSig probe provenance pkg := by
  intro packet
  have connectionLoop : Cont connection loop endpoint :=
    packet.right.right.right.right.right.right.right.left
  have endpointCurvature : Cont endpoint curvatureLedger compositionLedger :=
    packet.right.right.right.right.right.right.right.right.left
  cases cont_assoc_middle_exists connectionLoop endpointCurvature with
  | intro loopCurvature loopCurvatureRows =>
      have loopCurvatureUnary : UnaryHistory loopCurvature :=
        unary_cont_closed packet.right.right.left packet.right.right.right.right.left
          loopCurvatureRows.left
      exact Exists.intro loopCurvature
        (And.intro loopCurvatureUnary
          (And.intro loopCurvatureRows.left
            (And.intro loopCurvatureRows.right
              (And.intro loopCurvatureRows.right
                packet.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.HolonomyUp
