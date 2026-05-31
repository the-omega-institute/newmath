import BEDC.Derived.RegistryExportConsistencyGateUp.NoConflictExport

namespace BEDC.Derived.RegistryExportConsistencyGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegistryExportConsistencyGateSiblingDependency [AskSetup] [PackageSetup]
    {registry blocking status formalTarget audit noSmuggling transport replay provenance
      name siblingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegistryExportConsistencyGateAccepted registry blocking status formalTarget audit
        noSmuggling transport replay provenance name bundle pkg →
      Cont audit noSmuggling siblingRead →
        PkgSig bundle siblingRead pkg →
          UnaryHistory registry ∧ UnaryHistory blocking ∧ UnaryHistory status ∧
            UnaryHistory formalTarget ∧ UnaryHistory audit ∧ UnaryHistory noSmuggling ∧
              UnaryHistory siblingRead ∧ hsame blocking registry ∧ hsame audit status ∧
                hsame noSmuggling formalTarget ∧ Cont audit noSmuggling siblingRead ∧
                  Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle siblingRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame
  intro accepted auditNoSmuggling siblingPkg
  obtain ⟨registryUnary, blockingUnary, statusUnary, formalTargetUnary, auditUnary,
    noSmugglingUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    blockingRegistry, auditStatus, noSmugglingFormalTarget, transportReplayProvenance,
    provenancePkg, namePkg⟩ := accepted
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed auditUnary noSmugglingUnary auditNoSmuggling
  exact
    ⟨registryUnary, blockingUnary, statusUnary, formalTargetUnary, auditUnary,
      noSmugglingUnary, siblingUnary, blockingRegistry, auditStatus,
      noSmugglingFormalTarget, auditNoSmuggling, transportReplayProvenance, provenancePkg,
      namePkg, siblingPkg⟩

end BEDC.Derived.RegistryExportConsistencyGateUp
