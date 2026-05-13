import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApophaticSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApophaticSocketCarrier [AskSetup] [PackageSetup]
    (socketKind supplyShape auditGate site transport replay provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socketKind ∧ UnaryHistory supplyShape ∧ UnaryHistory auditGate ∧
    UnaryHistory site ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ hsame nameCert auditGate ∧
        Cont socketKind supplyShape auditGate ∧ Cont auditGate site replay ∧
          Cont replay provenance nameCert ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle nameCert pkg

theorem ApophaticSocketCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {socketKind supplyShape auditGate site transport replay provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticSocketCarrier socketKind supplyShape auditGate site transport replay provenance
        nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          ApophaticSocketCarrier socketKind supplyShape auditGate site transport replay
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist => hsame row auditGate ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameCert)
        hsame ∧ UnaryHistory socketKind ∧ UnaryHistory supplyShape ∧
          UnaryHistory auditGate ∧ UnaryHistory site ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨socketKindUnary, supplyShapeUnary, auditGateUnary, siteUnary, _transportUnary,
    _replayUnary, _provenanceUnary, nameCertUnary, nameCertAuditGate, _kindSupplyGate,
    _gateSiteReplay, _replayProvenanceNameCert, provenancePkg, _nameCertPkg⟩ := carrier
  have sourceNameCert :
      (fun row : BHist =>
        ApophaticSocketCarrier socketKind supplyShape auditGate site transport replay
          provenance nameCert bundle pkg ∧ hsame row nameCert) nameCert := by
    exact And.intro carrierWitness (hsame_refl nameCert)
  have core :
      NameCert
        (fun row : BHist =>
          ApophaticSocketCarrier socketKind supplyShape auditGate site transport replay
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro nameCert sourceNameCert
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameHNameCert : hsame h nameCert := sourceH.right
        have sameKNameCert : hsame k nameCert :=
          hsame_trans (hsame_symm sameHK) sameHNameCert
        exact And.intro sourceH.left sameKNameCert
    }
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticSocketCarrier socketKind supplyShape auditGate site transport replay
            provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist => hsame row auditGate ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row nameCert)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        have rowAuditGate : hsame row auditGate :=
          hsame_trans source.right nameCertAuditGate
        have rowUnary : UnaryHistory row :=
          unary_transport nameCertUnary (hsame_symm source.right)
        exact And.intro rowAuditGate rowUnary
      ledger_sound := by
        intro row source
        exact And.intro provenancePkg source.right
    }
  exact ⟨cert, socketKindUnary, supplyShapeUnary, auditGateUnary, siteUnary, provenancePkg⟩

end BEDC.Derived.ApophaticSocketUp
