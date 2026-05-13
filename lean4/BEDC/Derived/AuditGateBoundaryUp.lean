import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive AuditGateBoundaryUp : Type where
  | mk
      (sourceScan dependencyReport targetAudit originLedger transport continuation provenance gap name :
        BHist) :
      AuditGateBoundaryUp

def AuditGateBoundaryCarrier [AskSetup] [PackageSetup]
    (sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceScan ∧ UnaryHistory dependencyReport ∧ UnaryHistory markerResolution ∧
    UnaryHistory originLedger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory gap ∧ UnaryHistory nameCert ∧
        hsame dependencyReport gap ∧ hsame nameCert gap ∧
          Cont sourceScan dependencyReport markerResolution ∧
            Cont markerResolution originLedger transport ∧ Cont transport route provenance ∧
              Cont provenance gap nameCert ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle nameCert pkg

theorem AuditGateBoundaryCarrier_axiom_purity_soundness [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        (fun row : BHist => hsame row gap ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row dependencyReport)
        hsame := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, dependencyUnary, _markerUnary, _originUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, provenancePkg, _namePkg⟩ := carrier
  have sourceDependency :
      (fun row : BHist =>
        AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
          transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        dependencyReport := by
    exact And.intro carrierWitness (hsame_refl dependencyReport)
  have core :
      NameCert
        (fun row : BHist =>
          AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger
            transport route provenance gap nameCert bundle pkg ∧ hsame row dependencyReport)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro dependencyReport sourceDependency
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameRowDependency : hsame row dependencyReport := sourceRow.right
        have sameOtherDependency : hsame other dependencyReport :=
          hsame_trans (hsame_symm same) sameRowDependency
        exact And.intro sourceRow.left sameOtherDependency
    }
  exact {
    core := core
    pattern_sound := by
      intro row sourceRow
      have rowGap : hsame row gap :=
        hsame_trans sourceRow.right dependencyGap
      have rowUnary : UnaryHistory row :=
        unary_transport dependencyUnary (hsame_symm sourceRow.right)
      exact And.intro rowGap rowUnary
    ledger_sound := by
      intro row sourceRow
      exact And.intro provenancePkg sourceRow.right
  }

end BEDC.Derived.AuditGateBoundaryUp
