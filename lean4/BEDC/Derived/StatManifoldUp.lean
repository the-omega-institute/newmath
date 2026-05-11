import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StatManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StatManifoldCarrier [AskSetup] [PackageSetup]
    (manifold fisher theta distribution metric primal dual provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory theta ∧
    UnaryHistory distribution ∧ UnaryHistory metric ∧ UnaryHistory primal ∧
      UnaryHistory dual ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
        Cont theta distribution metric ∧ Cont metric primal dual ∧
          Cont manifold fisher provenance ∧ Cont provenance dual ledger ∧
            PkgSig bundle ledger pkg

def StatManifoldDependencyLedgerPacket
    (manifold fisher metric connection dualConnection provenance ledger : BHist) : Prop :=
  Cont manifold fisher metric ∧ Cont metric connection ledger ∧
    Cont ledger dualConnection provenance

theorem StatManifoldDependencyLedgerPacket_public_projection
    {manifold fisher metric connection dualConnection provenance ledger : BHist} :
    StatManifoldDependencyLedgerPacket manifold fisher metric connection dualConnection provenance
      ledger ->
      hsame metric (append manifold fisher) ∧ hsame ledger (append metric connection) ∧
        hsame provenance (append ledger dualConnection) ∧
          SemanticNameCert (fun row : BHist => row = ledger)
            (fun row : BHist => row = ledger)
            (fun row : BHist => row = ledger) hsame := by
  intro packet
  cases packet with
  | intro metricRow packetRest =>
      cases packetRest with
      | intro ledgerRow provenanceRow =>
          constructor
          · exact metricRow
          · constructor
            · exact ledgerRow
            · constructor
              · exact provenanceRow
              · exact {
                  core := {
                    carrier_inhabited := ⟨ledger, rfl⟩
                    equiv_refl := by
                      intro row _source
                      exact hsame_refl row
                    equiv_symm := by
                      intro _row _row' same
                      exact hsame_symm same
                    equiv_trans := by
                      intro _row _row' _row'' sameLeft sameRight
                      exact hsame_trans sameLeft sameRight
                    carrier_respects_equiv := by
                      intro _row _row' same source
                      exact (hsame_symm same).trans source
                  }
                  pattern_sound := by
                    intro _row source
                    exact source
                  ledger_sound := by
                    intro _row source
                    exact source
                }

def StatManifoldBHistPacket [AskSetup] [PackageSetup]
    (manifold fisher parameter distribution metric primalConnection dualConnection provenance
      ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory parameter ∧
    UnaryHistory distribution ∧ UnaryHistory primalConnection ∧ UnaryHistory provenance ∧
      Cont fisher parameter metric ∧ Cont metric primalConnection dualConnection ∧
        Cont provenance dualConnection ledger ∧ Cont ledger manifold endpoint ∧
          PkgSig bundle endpoint pkg

theorem StatManifoldBHistPacket_ledger_exactness [AskSetup] [PackageSetup]
    {manifold fisher parameter distribution metric primalConnection dualConnection provenance
      ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldBHistPacket manifold fisher parameter distribution metric primalConnection
        dualConnection provenance ledger endpoint bundle pkg ->
      hsame metric (append fisher parameter) ∧
        hsame dualConnection (append metric primalConnection) ∧
          hsame ledger (append provenance dualConnection) ∧
            hsame endpoint (append ledger manifold) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have metricRow : Cont fisher parameter metric :=
    packet.right.right.right.right.right.right.left
  have dualConnectionRow : Cont metric primalConnection dualConnection :=
    packet.right.right.right.right.right.right.right.left
  have ledgerRow : Cont provenance dualConnection ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont ledger manifold endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  exact And.intro metricRow
    (And.intro dualConnectionRow
      (And.intro ledgerRow
        (And.intro endpointRow
          packet.right.right.right.right.right.right.right.right.right.right)))

def StatManifoldCarrierPacket [AskSetup] [PackageSetup]
    (manifold fisher theta distribution metric connection dualConnection provenance ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory theta ∧
    UnaryHistory distribution ∧ UnaryHistory metric ∧ UnaryHistory connection ∧
      UnaryHistory dualConnection ∧ Cont manifold fisher ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem StatManifoldCarrierPacket_ledger_exactness [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric connection dualConnection provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldCarrierPacket manifold fisher theta distribution metric connection dualConnection
        provenance ledger endpoint bundle pkg ->
      UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory metric ∧
        UnaryHistory connection ∧ UnaryHistory dualConnection ∧ Cont manifold fisher ledger ∧
          hsame ledger (append manifold fisher) ∧ Cont provenance ledger endpoint ∧
            hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact And.intro packet.left
    (And.intro packet.right.left
      (And.intro packet.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.right.right.left
                  (And.intro packet.right.right.right.right.right.right.right.right.left
                    packet.right.right.right.right.right.right.right.right.right))))))))

def StatManifoldPacket [AskSetup] [PackageSetup]
    (manifold fisher theta distribution metric primal dual provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory fisher ∧ UnaryHistory theta ∧
    UnaryHistory distribution ∧ UnaryHistory metric ∧ UnaryHistory primal ∧
      UnaryHistory dual ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
        UnaryHistory endpoint ∧ hsame metric (append fisher distribution) ∧
          Cont (append (append manifold fisher) theta) ledger endpoint ∧
            PkgSig bundle endpoint pkg

theorem StatManifoldCarrier_classifier_transport [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric primal dual provenance ledger manifold' fisher'
      theta' distribution' metric' primal' dual' provenance' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldCarrier manifold fisher theta distribution metric primal dual provenance ledger
        bundle pkg ->
      hsame manifold manifold' ->
        hsame fisher fisher' ->
          hsame theta theta' ->
            hsame distribution distribution' ->
              hsame primal primal' ->
                Cont theta' distribution' metric' ->
                  Cont metric' primal' dual' ->
                    Cont manifold' fisher' provenance' ->
                      Cont provenance' dual' ledger' ->
                        PkgSig bundle ledger' pkg ->
                          StatManifoldCarrier manifold' fisher' theta' distribution' metric' primal'
                              dual' provenance' ledger' bundle pkg ∧
                            hsame metric metric' ∧ hsame dual dual' ∧
                              hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro carrier sameManifold sameFisher sameTheta sameDistribution samePrimal metricRow'
    dualRow' provenanceRow' ledgerRow' pkgSig'
  have manifoldUnary' : UnaryHistory manifold' :=
    unary_transport carrier.left sameManifold
  have fisherUnary' : UnaryHistory fisher' :=
    unary_transport carrier.right.left sameFisher
  have thetaUnary' : UnaryHistory theta' :=
    unary_transport carrier.right.right.left sameTheta
  have distributionUnary' : UnaryHistory distribution' :=
    unary_transport carrier.right.right.right.left sameDistribution
  have metricUnary' : UnaryHistory metric' :=
    unary_cont_closed thetaUnary' distributionUnary' metricRow'
  have primalUnary' : UnaryHistory primal' :=
    unary_transport carrier.right.right.right.right.right.left samePrimal
  have dualUnary' : UnaryHistory dual' :=
    unary_cont_closed metricUnary' primalUnary' dualRow'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed manifoldUnary' fisherUnary' provenanceRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed provenanceUnary' dualUnary' ledgerRow'
  have sameMetric : hsame metric metric' :=
    cont_respects_hsame sameTheta sameDistribution
      carrier.right.right.right.right.right.right.right.right.right.left metricRow'
  have sameDual : hsame dual dual' :=
    cont_respects_hsame sameMetric samePrimal
      carrier.right.right.right.right.right.right.right.right.right.right.left dualRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameManifold sameFisher
      carrier.right.right.right.right.right.right.right.right.right.right.right.left provenanceRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProvenance sameDual
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.left ledgerRow'
  constructor
  · exact
      And.intro manifoldUnary'
        (And.intro fisherUnary'
          (And.intro thetaUnary'
            (And.intro distributionUnary'
              (And.intro metricUnary'
                (And.intro primalUnary'
                  (And.intro dualUnary'
                    (And.intro provenanceUnary'
                      (And.intro ledgerUnary'
      (And.intro metricRow'
        (And.intro dualRow'
          (And.intro provenanceRow'
            (And.intro ledgerRow' pkgSig'))))))))))))
  · exact And.intro sameMetric (And.intro sameDual (And.intro sameProvenance sameLedger))

theorem StatManifoldCarrier_dependency_source_scope_transport [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric primal dual provenance ledger manifold' fisher'
      provenance' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldCarrier manifold fisher theta distribution metric primal dual provenance ledger
        bundle pkg ->
      hsame manifold manifold' ->
        hsame fisher fisher' ->
          Cont manifold' fisher' provenance' ->
            Cont provenance' dual ledger' ->
              PkgSig bundle ledger' pkg ->
                hsame provenance provenance' ∧
                  hsame ledger ledger' ∧
                    StatManifoldCarrier manifold' fisher' theta distribution metric primal dual
                      provenance' ledger' bundle pkg := by
  intro carrier sameManifold sameFisher provenanceRow' ledgerRow' pkgSig'
  rcases carrier with
    ⟨manifoldUnary, fisherUnary, thetaUnary, distributionUnary, metricUnary, primalUnary,
      dualUnary, _provenanceUnary, _ledgerUnary, metricRow, dualRow, provenanceRow, ledgerRow,
      _pkgSig⟩
  have manifoldUnary' : UnaryHistory manifold' :=
    unary_transport manifoldUnary sameManifold
  have fisherUnary' : UnaryHistory fisher' :=
    unary_transport fisherUnary sameFisher
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed manifoldUnary' fisherUnary' provenanceRow'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed provenanceUnary' dualUnary ledgerRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameManifold sameFisher provenanceRow provenanceRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProvenance (hsame_refl dual) ledgerRow ledgerRow'
  have carrier' :
      StatManifoldCarrier manifold' fisher' theta distribution metric primal dual provenance'
        ledger' bundle pkg :=
    And.intro manifoldUnary'
      (And.intro fisherUnary'
        (And.intro thetaUnary
          (And.intro distributionUnary
            (And.intro metricUnary
              (And.intro primalUnary
                (And.intro dualUnary
                  (And.intro provenanceUnary'
                    (And.intro ledgerUnary'
                      (And.intro metricRow
                        (And.intro dualRow
                          (And.intro provenanceRow' (And.intro ledgerRow' pkgSig'))))))))))))
  exact And.intro sameProvenance (And.intro sameLedger carrier')

theorem StatManifoldFisherManifoldSource_scope_transport [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric primal dual provenance ledger manifold' fisher'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldCarrier manifold fisher theta distribution metric primal dual provenance ledger
        bundle pkg ->
      hsame manifold manifold' ->
        hsame fisher fisher' ->
          Cont manifold' fisher' provenance' ->
            UnaryHistory manifold' ∧ UnaryHistory fisher' ∧ UnaryHistory provenance' ∧
              hsame provenance provenance' ∧ PkgSig bundle ledger pkg := by
  intro carrier sameManifold sameFisher provenanceRow'
  have manifoldUnary' : UnaryHistory manifold' :=
    unary_transport carrier.left sameManifold
  have fisherUnary' : UnaryHistory fisher' :=
    unary_transport carrier.right.left sameFisher
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed manifoldUnary' fisherUnary' provenanceRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameManifold sameFisher
      carrier.right.right.right.right.right.right.right.right.right.right.right.left
      provenanceRow'
  exact And.intro manifoldUnary'
    (And.intro fisherUnary'
      (And.intro provenanceUnary'
        (And.intro sameProvenance
          carrier.right.right.right.right.right.right.right.right.right.right.right.right.right)))

theorem StatManifoldPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {manifold fisher theta distribution metric primal dual provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StatManifoldPacket manifold fisher theta distribution metric primal dual provenance ledger
      endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              StatManifoldPacket manifold fisher theta distribution metric primal dual provenance
                ledger e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              StatManifoldPacket manifold fisher theta distribution metric primal dual provenance
                ledger e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              StatManifoldPacket manifold fisher theta distribution metric primal dual provenance
                ledger e bundle pkg ∧ hsame row e)
          hsame ∧
        hsame metric (append fisher distribution) ∧
          Cont (append (append manifold fisher) theta) ledger endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro endpoint (Exists.intro endpoint (And.intro packet (hsame_refl endpoint)))
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
          cases source with
          | intro e data =>
              exact Exists.intro e
                (And.intro data.left (hsame_trans (hsame_symm same) data.right))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · exact
      And.intro packet.right.right.right.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right.right.right.right)

end BEDC.Derived.StatManifoldUp
