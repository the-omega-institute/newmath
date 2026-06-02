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

def RegistryExportConsistencyGateCarrier [AskSetup] [PackageSetup]
    (registry blocking status formalTarget audit noSmuggling transport replay provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory registry ∧ UnaryHistory blocking ∧ UnaryHistory status ∧
    UnaryHistory formalTarget ∧ UnaryHistory audit ∧ UnaryHistory noSmuggling ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont registry status formalTarget ∧
          Cont audit noSmuggling blocking ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

theorem RegistryExportConsistencyGateCarrier_semantic_namecert [AskSetup] [PackageSetup]
    {registry blocking status formalTarget audit noSmuggling transport replay provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegistryExportConsistencyGateCarrier registry blocking status formalTarget audit
        noSmuggling transport replay provenance name bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row registry ∨ hsame row status ∨ hsame row formalTarget)
        (fun row : BHist =>
          hsame row registry ∨ hsame row status ∨ hsame row formalTarget)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨registryUnary, _blockingUnary, statusUnary, formalTargetUnary, _auditUnary,
    _noSmugglingUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _statusRoute, _auditRoute, provenancePkg, namePkg⟩ := carrier
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
            | inr rowFormalTarget =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowFormalTarget))
    }
    pattern_sound := by
      intro row source
      exact source
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
            | inr rowFormalTarget =>
                exact unary_transport formalTargetUnary (hsame_symm rowFormalTarget)
      exact ⟨rowUnary, provenancePkg, namePkg⟩
  }

end BEDC.Derived.RegistryExportConsistencyGateUp
