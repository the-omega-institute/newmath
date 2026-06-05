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

theorem MetacicNormalizationAuditCarrier_confluence_boundary [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row confluence ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row confluence ∨ hsame row ledger ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row confluence ∧ Cont confluence audit ledger ∧
              PkgSig bundle provenance pkg)
          hsame ∧ UnaryHistory confluence := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨_kernelUnary, _normalizerUnary, _frontierUnary, _snUnary, confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row confluence ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row confluence ∨ hsame row ledger ∨ hsame row provenance)
        (fun row : BHist =>
          hsame row confluence ∧ Cont confluence audit ledger ∧
            PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro confluence ⟨hsame_refl confluence, confluenceUnary⟩
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
      exact Or.inl sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, confluenceAuditLedger, provenancePkg⟩
  }
  exact ⟨cert, confluenceUnary⟩

theorem MetacicNormalizationAuditCarrier_closed_term_projection_route [AskSetup]
    [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName closedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      Cont audit replay closedRead →
        PkgSig bundle closedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row closedRead ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row audit ∨ hsame row closedRead ∨ hsame row provenance)
              (fun row : BHist =>
                hsame row closedRead ∧ Cont audit replay closedRead ∧
                  PkgSig bundle provenance pkg)
              hsame ∧ UnaryHistory audit ∧ UnaryHistory closedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier auditReplayClosed closedPkg
  obtain ⟨_kernelUnary, _normalizerUnary, _frontierUnary, _snUnary, _confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, replayUnary, provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed auditUnary replayUnary auditReplayClosed
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row closedRead ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row audit ∨ hsame row closedRead ∨ hsame row provenance)
        (fun row : BHist =>
          hsame row closedRead ∧ Cont audit replay closedRead ∧
            PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro closedRead
        ⟨hsame_refl closedRead, closedUnary, closedPkg⟩
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
        intro _row other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inl sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, auditReplayClosed, provenancePkg⟩
  }
  exact ⟨cert, auditUnary, closedUnary⟩

theorem MetacicNormalizationAuditCarrier_ledger_policy [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      Cont audit ledger ledgerRead →
        PkgSig bundle ledgerRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row ledgerRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨
                  hsame row sn ∨ hsame row confluence ∨ hsame row audit ∨
                    hsame row ledger ∨ hsame row replay ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row ledgerRead)
              (fun row : BHist =>
                hsame row ledgerRead ∧ Cont audit ledger ledgerRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory ledgerRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier auditLedgerRead ledgerReadPkg
  obtain ⟨_kernelUnary, _normalizerUnary, _frontierUnary, _snUnary, _confluenceUnary,
    auditUnary, ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, localNamePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed auditUnary ledgerUnary auditLedgerRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledgerRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row kernel ∨ hsame row normalizer ∨ hsame row frontier ∨ hsame row sn ∨
              hsame row confluence ∨ hsame row audit ∨ hsame row ledger ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row ledgerRead)
          (fun row : BHist =>
            hsame row ledgerRead ∧ Cont audit ledger ledgerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead
        ⟨hsame_refl ledgerRead, ledgerReadUnary, ledgerReadPkg⟩
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
        intro _row other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, auditLedgerRead, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, ledgerReadUnary, provenancePkg, localNamePkg⟩

theorem MetacicNormalizationAuditResidualBudgetObligation [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName residualRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      Cont audit replay residualRead →
        Cont residualRead confluence budgetRead →
          PkgSig bundle budgetRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row budgetRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                    hsame row confluence ∨ hsame row residualRead ∨
                      hsame row budgetRead ∨ hsame row provenance)
                (fun row : BHist =>
                  hsame row budgetRead ∧ Cont frontier sn audit ∧
                    Cont audit replay residualRead ∧
                      Cont residualRead confluence budgetRead ∧
                        PkgSig bundle provenance pkg)
                hsame ∧ UnaryHistory audit ∧ UnaryHistory residualRead ∧
              UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier residualRoute budgetRoute budgetPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed auditUnary replayUnary residualRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed residualUnary confluenceUnary budgetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row budgetRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
              hsame row confluence ∨ hsame row residualRead ∨ hsame row budgetRead ∨
                hsame row provenance)
          (fun row : BHist =>
            hsame row budgetRead ∧ Cont frontier sn audit ∧
              Cont audit replay residualRead ∧ Cont residualRead confluence budgetRead ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead
        ⟨hsame_refl budgetRead, budgetUnary, budgetPkg⟩
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
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, frontierSnAudit, residualRoute, budgetRoute, provenancePkg⟩
  }
  exact ⟨cert, auditUnary, residualUnary, budgetUnary⟩

theorem MetacicNormalizationAuditCarrier_residual_budget_obligation [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      Cont audit ledger residualRead →
        PkgSig bundle residualRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                  hsame row ledger ∨ hsame row residualRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont frontier sn audit ∧
                  Cont audit ledger residualRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle residualRead pkg)
              hsame ∧ UnaryHistory residualRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier auditLedgerResidual residualPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed auditUnary ledgerUnary auditLedgerResidual
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
              hsame row ledger ∨ hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontier sn audit ∧
              Cont audit ledger residualRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle residualRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead
        ⟨hsame_refl residualRead, residualUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, frontierSnAudit, auditLedgerResidual, provenancePkg,
          residualPkg⟩
  }
  exact ⟨cert, residualUnary, provenancePkg⟩

end MetacicNormalizationAuditUp
end BEDC.Derived
