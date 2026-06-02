import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetacicNormalizationAuditUp [AskSetup] [PackageSetup]
    (kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  UnaryHistory kernel ∧ UnaryHistory normalizer ∧ UnaryHistory frontier ∧ UnaryHistory sn ∧
    UnaryHistory confluence ∧ UnaryHistory audit ∧ UnaryHistory ledger ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont kernel normalizer frontier ∧ Cont frontier sn audit ∧
          Cont confluence audit ledger ∧ hsame transport replay ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

namespace MetacicNormalizationAuditUp

theorem MetacicNormalizationAuditCarrier_obligation_surface [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
            transport replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
            transport replay provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
            transport replay provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  have carrierWitness :
      MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg :=
    carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrierWitness, hsame_refl localName⟩
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
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem MetacicNormalizationAuditCarrier_sn_scope [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row audit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row audit ∧ Cont frontier sn audit ∧ PkgSig bundle provenance pkg)
          hsame ∧ UnaryHistory audit := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row audit ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨ hsame row provenance)
        (fun row : BHist =>
          hsame row audit ∧ Cont frontier sn audit ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro audit ⟨hsame_refl audit, auditUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inl sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, frontierSnAudit, provenancePkg⟩
  }
  exact ⟨cert, auditUnary⟩

end MetacicNormalizationAuditUp
end BEDC.Derived
