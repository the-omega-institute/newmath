import BEDC.Derived.RealityConstrainedTowerCompressionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedTowerCompressionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealityConstrainedTowerCompressionCarrier [AskSetup] [PackageSetup]
    (S T O F A M C L E R P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory O ∧ UnaryHistory F ∧
      UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory C ∧ UnaryHistory L ∧
        UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory N ∧
          Cont S T O ∧ Cont O F A ∧ Cont A M C ∧ Cont C L E ∧ Cont E R P ∧
            Cont P N L ∧ hsame E (append C L) ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg

theorem RealityConstrainedTowerCompressionNameCert_obligations [AskSetup] [PackageSetup]
    {S T O F A M C L E R P N readLedger readEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg →
      Cont E L readLedger →
        Cont readLedger C readEndpoint →
          PkgSig bundle readEndpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N
                    bundle pkg ∧ hsame row E)
                (fun row : BHist => hsame row E ∧ UnaryHistory row)
                (fun _row : BHist =>
                  Cont E L readLedger ∧ Cont readLedger C readEndpoint ∧
                    PkgSig bundle readEndpoint pkg)
                hsame ∧
              UnaryHistory E ∧ UnaryHistory readLedger ∧ UnaryHistory readEndpoint := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerRoute endpointRoute endpointPkg
  have carrierPacket :
      RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _towerUnary, _observerUnary, _fitUnary, _approxUnary,
    _auditUnary, classifierUnary, ledgerUnary, endpointUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _sourceTowerObserver, _observerFitApprox,
    _approxAuditClassifier, _classifierLedgerEndpoint, _endpointReplayProvenance,
    _provenanceNameLedger, _endpointSameClassifierLedger, _endpointPkg, _namePkg⟩ := carrier
  have readLedgerUnary : UnaryHistory readLedger :=
    unary_cont_closed endpointUnary ledgerUnary ledgerRoute
  have readEndpointUnary : UnaryHistory readEndpoint :=
    unary_cont_closed readLedgerUnary classifierUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg ∧
              hsame row E)
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont E L readLedger ∧ Cont readLedger C readEndpoint ∧
              PkgSig bundle readEndpoint pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro E ⟨carrierPacket, hsame_refl E⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, unary_transport endpointUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨ledgerRoute, endpointRoute, endpointPkg⟩
    }
  exact ⟨cert, endpointUnary, readLedgerUnary, readEndpointUnary⟩

theorem RealityConstrainedTowerCompressionLedger_nonescape [AskSetup] [PackageSetup]
    {S T O F A M C L E R P N readLedger readEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg →
      Cont E L readLedger →
        Cont readLedger C readEndpoint →
          PkgSig bundle readEndpoint pkg →
            UnaryHistory L ∧ UnaryHistory E ∧ UnaryHistory readLedger ∧
              UnaryHistory readEndpoint ∧ Cont E L readLedger ∧
                Cont readLedger C readEndpoint ∧ hsame E (append C L) ∧
                  PkgSig bundle readEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro carrier ledgerRoute endpointRoute endpointPkg
  obtain ⟨_sourceUnary, _towerUnary, _observerUnary, _fitUnary, _approxUnary,
    _auditUnary, classifierUnary, ledgerUnary, endpointUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _sourceTowerObserver, _observerFitApprox,
    _approxAuditClassifier, _classifierLedgerEndpoint, _endpointReplayProvenance,
    _provenanceNameLedger, endpointSameClassifierLedger, _endpointPkg, _namePkg⟩ := carrier
  have readLedgerUnary : UnaryHistory readLedger :=
    unary_cont_closed endpointUnary ledgerUnary ledgerRoute
  have readEndpointUnary : UnaryHistory readEndpoint :=
    unary_cont_closed readLedgerUnary classifierUnary endpointRoute
  exact
    ⟨ledgerUnary, endpointUnary, readLedgerUnary, readEndpointUnary, ledgerRoute,
      endpointRoute, endpointSameClassifierLedger, endpointPkg⟩

theorem RealityConstrainedTowerCompressionClassifier_accountability [AskSetup] [PackageSetup]
    {S T O F A M C L E R P N classifierRead ledgerRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg →
      Cont A M classifierRead →
        hsame classifierRead C →
          Cont C L ledgerRead →
            Cont ledgerRead E endpointRead →
              PkgSig bundle endpointRead pkg →
                UnaryHistory C ∧ UnaryHistory classifierRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory endpointRead ∧ Cont A M classifierRead ∧
                    hsame classifierRead C ∧ Cont C L ledgerRead ∧
                      Cont ledgerRead E endpointRead ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro carrier approxAuditClassifier classifierSame ledgerRoute endpointRoute endpointPkg
  obtain ⟨_sourceUnary, _towerUnary, _observerUnary, _fitUnary, _approxUnary,
    _auditUnary, classifierUnary, ledgerUnary, endpointUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _sourceTowerObserver, _observerFitApprox,
    _carrierApproxAuditClassifier, _classifierLedgerEndpoint, _endpointReplayProvenance,
    _provenanceNameLedger, _endpointSameClassifierLedger, _endpointPkg, _namePkg⟩ := carrier
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_transport_symm classifierUnary classifierSame
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed classifierUnary ledgerUnary ledgerRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed ledgerReadUnary endpointUnary endpointRoute
  exact
    ⟨classifierUnary, classifierReadUnary, ledgerReadUnary, endpointReadUnary,
      approxAuditClassifier, classifierSame, ledgerRoute, endpointRoute, endpointPkg⟩

theorem RealityConstrainedTowerCompressionScoped_source_exactness [AskSetup] [PackageSetup]
    {S T O F A M C L E R P N readLedger readEndpoint scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg →
      Cont E L readLedger →
        Cont readLedger C readEndpoint →
          Cont readEndpoint R scopedRead →
            PkgSig bundle scopedRead pkg →
              UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory O ∧ UnaryHistory F ∧
                UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory C ∧ UnaryHistory L ∧
                  UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory N ∧
                    UnaryHistory readLedger ∧ UnaryHistory readEndpoint ∧
                      UnaryHistory scopedRead ∧ Cont E L readLedger ∧
                        Cont readLedger C readEndpoint ∧ Cont readEndpoint R scopedRead ∧
                          hsame E (append C L) ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro carrier ledgerRoute endpointRoute scopedRoute scopedPkg
  obtain ⟨sourceUnary, towerUnary, observerUnary, fitUnary, approxUnary, auditUnary,
    classifierUnary, ledgerUnary, endpointUnary, replayUnary, provenanceUnary, nameUnary,
    _sourceTowerObserver, _observerFitApprox, _approxAuditClassifier,
    _classifierLedgerEndpoint, _endpointReplayProvenance, _provenanceNameLedger,
    endpointSameClassifierLedger, provenancePkg, _namePkg⟩ := carrier
  have readLedgerUnary : UnaryHistory readLedger :=
    unary_cont_closed endpointUnary ledgerUnary ledgerRoute
  have readEndpointUnary : UnaryHistory readEndpoint :=
    unary_cont_closed readLedgerUnary classifierUnary endpointRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed readEndpointUnary replayUnary scopedRoute
  exact
    ⟨sourceUnary, towerUnary, observerUnary, fitUnary, approxUnary, auditUnary,
      classifierUnary, ledgerUnary, endpointUnary, replayUnary, provenanceUnary, nameUnary,
      readLedgerUnary, readEndpointUnary, scopedReadUnary, ledgerRoute, endpointRoute,
      scopedRoute, endpointSameClassifierLedger, provenancePkg, scopedPkg⟩

theorem RealityConstrainedTowerCompressionScoped_dependency_surface [AskSetup] [PackageSetup]
    {S T O F A M C L E R P N dependencyRead endpointRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg →
      Cont C L dependencyRead →
        Cont dependencyRead E endpointRead →
          Cont endpointRead R scopedRead →
            PkgSig bundle scopedRead pkg →
              UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory O ∧ UnaryHistory F ∧
                UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory C ∧ UnaryHistory L ∧
                  UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory N ∧
                    UnaryHistory dependencyRead ∧ UnaryHistory endpointRead ∧
                      UnaryHistory scopedRead ∧ Cont C L dependencyRead ∧
                        Cont dependencyRead E endpointRead ∧ Cont endpointRead R scopedRead ∧
                          hsame E (append C L) ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro carrier dependencyRoute endpointRoute scopedRoute scopedPkg
  obtain ⟨sourceUnary, towerUnary, observerUnary, fitUnary, approxUnary, auditUnary,
    classifierUnary, ledgerUnary, endpointUnary, replayUnary, provenanceUnary, nameUnary,
    _sourceTowerObserver, _observerFitApprox, _approxAuditClassifier,
    _classifierLedgerEndpoint, _endpointReplayProvenance, _provenanceNameLedger,
    endpointSameClassifierLedger, provenancePkg, _namePkg⟩ := carrier
  have dependencyReadUnary : UnaryHistory dependencyRead :=
    unary_cont_closed classifierUnary ledgerUnary dependencyRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed dependencyReadUnary endpointUnary endpointRoute
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed endpointReadUnary replayUnary scopedRoute
  exact
    ⟨sourceUnary, towerUnary, observerUnary, fitUnary, approxUnary, auditUnary,
      classifierUnary, ledgerUnary, endpointUnary, replayUnary, provenanceUnary, nameUnary,
      dependencyReadUnary, endpointReadUnary, scopedReadUnary, dependencyRoute,
      endpointRoute, scopedRoute, endpointSameClassifierLedger, provenancePkg, scopedPkg⟩

theorem RealityConstrainedTowerCompressionEndpoint_source_separation [AskSetup] [PackageSetup]
    {S T O F A M C L E R P N endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg →
      Cont C L E →
        Cont E R endpointRead →
          PkgSig bundle endpointRead pkg →
            UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory L ∧
              UnaryHistory endpointRead ∧ hsame E (append C L) ∧ Cont C L E ∧
                Cont E R endpointRead ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro carrier classifierLedgerEndpoint endpointReplay endpointPkg
  obtain ⟨sourceUnary, _towerUnary, _observerUnary, _fitUnary, _approxUnary,
    _auditUnary, _classifierUnary, ledgerUnary, endpointUnary, replayUnary,
    _provenanceUnary, _nameUnary, _sourceTowerObserver, _observerFitApprox,
    _approxAuditClassifier, _carrierClassifierLedgerEndpoint,
    _carrierEndpointReplayProvenance, _provenanceNameLedger,
    endpointSameClassifierLedger, _endpointPkg, _namePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplay
  exact
    ⟨sourceUnary, endpointUnary, ledgerUnary, endpointReadUnary,
      endpointSameClassifierLedger, classifierLedgerEndpoint, endpointReplay, endpointPkg⟩

theorem RealityConstrainedTowerCompressionDownstreamRouteExhaustion [AskSetup] [PackageSetup]
    {S T O F A M C L E R P N endpointRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedTowerCompressionCarrier S T O F A M C L E R P N bundle pkg →
      Cont E R endpointRead →
        Cont endpointRead P downstreamRead →
          PkgSig bundle downstreamRead pkg →
            UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory O ∧ UnaryHistory F ∧
              UnaryHistory A ∧ UnaryHistory M ∧ UnaryHistory C ∧ UnaryHistory L ∧
                UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory endpointRead ∧
                  UnaryHistory downstreamRead ∧ Cont E R endpointRead ∧
                    Cont endpointRead P downstreamRead ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro carrier endpointReplay downstreamRoute downstreamPkg
  obtain ⟨sourceUnary, towerUnary, observerUnary, fitUnary, approxUnary, auditUnary,
    classifierUnary, ledgerUnary, endpointUnary, replayUnary, provenanceUnary, nameUnary,
    _sourceTowerObserver, _observerFitApprox, _approxAuditClassifier,
    _classifierLedgerEndpoint, _endpointReplayProvenance, _provenanceNameLedger,
    _endpointSameClassifierLedger, _provenancePkg, namePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplay
  have downstreamReadUnary : UnaryHistory downstreamRead :=
    unary_cont_closed endpointReadUnary provenanceUnary downstreamRoute
  exact
    ⟨sourceUnary, towerUnary, observerUnary, fitUnary, approxUnary, auditUnary,
      classifierUnary, ledgerUnary, endpointUnary, replayUnary, endpointReadUnary,
      downstreamReadUnary, endpointReplay, downstreamRoute, namePkg, downstreamPkg⟩

end BEDC.Derived.RealityConstrainedTowerCompressionUp
