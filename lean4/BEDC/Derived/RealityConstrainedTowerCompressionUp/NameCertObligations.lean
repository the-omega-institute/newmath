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
          Cont P N L ∧ hsame E (append C L) ∧ PkgSig bundle E pkg

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
    _provenanceNameLedger, _endpointSameClassifierLedger, _endpointPkg⟩ := carrier
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

end BEDC.Derived.RealityConstrainedTowerCompressionUp
