import BEDC.Derived.RegistryExportConsistencyGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegistryExportConsistencyGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegistryExportConsistencyGateAccepted [AskSetup] [PackageSetup]
    (registry blocking status formalTarget audit noSmuggling transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame UnaryHistory
  UnaryHistory registry ∧ UnaryHistory blocking ∧ UnaryHistory status ∧
    UnaryHistory formalTarget ∧ UnaryHistory audit ∧ UnaryHistory noSmuggling ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ hsame blocking registry ∧ hsame audit status ∧
          hsame noSmuggling formalTarget ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem RegistryExportConsistencyGateNoConflictExport [AskSetup] [PackageSetup]
    {registry blocking status formalTarget audit noSmuggling transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegistryExportConsistencyGateAccepted registry blocking status formalTarget audit
        noSmuggling transport replay provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist => hsame row blocking ∨ hsame row audit ∨ hsame row noSmuggling)
        (fun row : BHist => hsame row registry ∨ hsame row status ∨ hsame row formalTarget)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro accepted
  obtain ⟨_registryUnary, blockingUnary, _statusUnary, _formalTargetUnary, auditUnary,
    noSmugglingUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    blockingRegistry, auditStatus, noSmugglingFormalTarget, _transportReplayProvenance,
    provenancePkg, namePkg⟩ := accepted
  exact {
    core := {
      carrier_inhabited := Exists.intro blocking (Or.inl (hsame_refl blocking))
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
        | inl rowBlocking =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) rowBlocking)
        | inr rest =>
            cases rest with
            | inl rowAudit =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowAudit))
            | inr rowNoSmuggling =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowNoSmuggling))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl rowBlocking =>
          exact Or.inl (hsame_trans rowBlocking blockingRegistry)
      | inr rest =>
          cases rest with
          | inl rowAudit =>
              exact Or.inr (Or.inl (hsame_trans rowAudit auditStatus))
          | inr rowNoSmuggling =>
              exact Or.inr (Or.inr (hsame_trans rowNoSmuggling noSmugglingFormalTarget))
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source with
        | inl rowBlocking =>
            exact unary_transport blockingUnary (hsame_symm rowBlocking)
        | inr rest =>
            cases rest with
            | inl rowAudit =>
                exact unary_transport auditUnary (hsame_symm rowAudit)
            | inr rowNoSmuggling =>
                exact unary_transport noSmugglingUnary (hsame_symm rowNoSmuggling)
      exact ⟨rowUnary, provenancePkg, namePkg⟩
  }

end BEDC.Derived.RegistryExportConsistencyGateUp
