import BEDC.Derived.RegistryExportConsistencyGateUp.Carrier

namespace BEDC.Derived.RegistryExportConsistencyGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegistryExportConsistencyGateClassifierSpec [AskSetup] [PackageSetup]
    (registry blocking status formalTarget audit noSmuggling transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  RegistryExportConsistencyGateCarrier registry blocking status formalTarget audit noSmuggling
      transport replay provenance name bundle pkg ∧
    hsame status registry ∧ hsame formalTarget status ∧ Cont status formalTarget audit

theorem RegistryExportConsistencyGateClassifierSpec_closure [AskSetup] [PackageSetup]
    {registry blocking status formalTarget audit noSmuggling transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegistryExportConsistencyGateClassifierSpec registry blocking status formalTarget audit
        noSmuggling transport replay provenance name bundle pkg →
      UnaryHistory registry ∧ UnaryHistory status ∧ UnaryHistory formalTarget ∧
        UnaryHistory audit ∧ hsame status registry ∧ hsame formalTarget status ∧
          Cont status formalTarget audit ∧ Cont registry status formalTarget ∧
            Cont audit noSmuggling blocking ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro classifier
  obtain ⟨carrier, statusRegistry, formalTargetStatus, statusFormalTargetAudit⟩ :=
    classifier
  obtain ⟨registryUnary, _blockingUnary, statusUnary, formalTargetUnary, auditUnary,
    _noSmugglingUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    registryStatusFormalTarget, auditNoSmugglingBlocking, provenancePkg, namePkg⟩ :=
      carrier
  exact
    ⟨registryUnary, statusUnary, formalTargetUnary, auditUnary, statusRegistry,
      formalTargetStatus, statusFormalTargetAudit, registryStatusFormalTarget,
      auditNoSmugglingBlocking, provenancePkg, namePkg⟩

end BEDC.Derived.RegistryExportConsistencyGateUp
