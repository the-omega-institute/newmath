import BEDC.Derived.RegistryExportConsistencyGateUp.Carrier
import BEDC.Derived.RegistryExportConsistencyGateUp.NoConflictExport

namespace BEDC.Derived.RegistryExportConsistencyGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegistryExportConsistencyGateClassifier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {registry blocking status formalTarget audit noSmuggling transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegistryExportConsistencyGateCarrier registry blocking status formalTarget audit
        noSmuggling transport replay provenance name bundle pkg →
      RegistryExportConsistencyGateAccepted registry blocking status formalTarget audit
        noSmuggling transport replay provenance name bundle pkg →
        SemanticNameCert
          (fun row : BHist =>
            hsame row registry ∨ hsame row status ∨ hsame row formalTarget ∨
              hsame row audit ∨ hsame row noSmuggling)
          (fun row : BHist =>
            hsame row registry ∨ hsame row status ∨ hsame row formalTarget)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier accepted
  obtain ⟨registryUnary, _blockingUnary, statusUnary, formalTargetUnary, auditUnary,
    noSmugglingUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _statusRoute, _auditRoute, provenancePkg, namePkg⟩ := carrier
  obtain ⟨_acceptedRegistryUnary, _acceptedBlockingUnary, _acceptedStatusUnary,
    _acceptedFormalTargetUnary, _acceptedAuditUnary, _acceptedNoSmugglingUnary,
    _acceptedTransportUnary, _acceptedReplayUnary, _acceptedProvenanceUnary,
    _acceptedNameUnary, _blockingRegistry, auditStatus, noSmugglingFormalTarget,
    _transportReplayProvenance, _acceptedProvenancePkg, _acceptedNamePkg⟩ := accepted
  exact {
    core := {
      carrier_inhabited := Exists.intro registry (Or.inl (hsame_refl registry))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        cases source with
        | inl rowRegistry =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowRegistry)
        | inr rest =>
            cases rest with
            | inl rowStatus =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowStatus))
            | inr rest =>
                cases rest with
                | inl rowFormalTarget =>
                    exact Or.inr
                      (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowFormalTarget)))
                | inr rest =>
                    cases rest with
                    | inl rowAudit =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowAudit))))
                    | inr rowNoSmuggling =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (hsame_trans (hsame_symm sameRows) rowNoSmuggling))))
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl rowRegistry =>
          exact Or.inl rowRegistry
      | inr rest =>
          cases rest with
          | inl rowStatus =>
              exact Or.inr (Or.inl rowStatus)
          | inr rest =>
              cases rest with
              | inl rowFormalTarget =>
                  exact Or.inr (Or.inr rowFormalTarget)
              | inr rest =>
                  cases rest with
                  | inl rowAudit =>
                      exact Or.inr (Or.inl (hsame_trans rowAudit auditStatus))
                  | inr rowNoSmuggling =>
                      exact Or.inr
                        (Or.inr (hsame_trans rowNoSmuggling noSmugglingFormalTarget))
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source with
        | inl rowRegistry =>
            exact unary_transport registryUnary (hsame_symm rowRegistry)
        | inr rest =>
            cases rest with
            | inl rowStatus =>
                exact unary_transport statusUnary (hsame_symm rowStatus)
            | inr rest =>
                cases rest with
                | inl rowFormalTarget =>
                    exact unary_transport formalTargetUnary (hsame_symm rowFormalTarget)
                | inr rest =>
                    cases rest with
                    | inl rowAudit =>
                        exact unary_transport auditUnary (hsame_symm rowAudit)
                    | inr rowNoSmuggling =>
                        exact unary_transport noSmugglingUnary (hsame_symm rowNoSmuggling)
      exact ⟨rowUnary, provenancePkg, namePkg⟩
  }

end BEDC.Derived.RegistryExportConsistencyGateUp
