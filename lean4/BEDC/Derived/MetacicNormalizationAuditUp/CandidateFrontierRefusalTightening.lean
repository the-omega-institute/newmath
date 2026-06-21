import BEDC.Derived.MetacicNormalizationAuditUp.CandidateFrontierRefusal

namespace BEDC.Derived.MetacicNormalizationAuditUp.CandidateFrontierRefusalTightening

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateFrontierRefusalTightening
    [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName closedRead refusalRead named fallback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit
        ledger transport replay provenance localName bundle pkg →
      Cont frontier sn audit →
        Cont audit replay closedRead →
          Cont closedRead localName refusalRead →
            Cont refusalRead provenance named →
              Cont localName provenance fallback →
                PkgSig bundle named pkg →
                  PkgSig bundle fallback pkg →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row fallback ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                        (fun row : BHist =>
                          hsame row localName ∨ hsame row provenance ∨
                            hsame row fallback ∨ hsame row named)
                        (fun row : BHist =>
                          hsame row fallback ∧ Cont localName provenance fallback ∧
                            PkgSig bundle fallback pkg)
                        hsame ∧
                      UnaryHistory fallback := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier _frontierSnAudit _auditReplayClosed _closedLocalRefusal
    _refusalProvenanceNamed localProvenanceFallback _namedPkg fallbackPkg
  obtain ⟨_kernelUnary, _normalizerUnary, _frontierUnary, _snUnary, _confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, _replayUnary, provenanceUnary,
    localNameUnary, _kernelNormalizerFrontier, _carrierFrontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, _provenancePkg, _localNamePkg⟩ :=
      carrier
  have fallbackUnary : UnaryHistory fallback :=
    unary_cont_closed localNameUnary provenanceUnary localProvenanceFallback
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row fallback ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row localName ∨ hsame row provenance ∨ hsame row fallback ∨
              hsame row named)
          (fun row : BHist =>
            hsame row fallback ∧ Cont localName provenance fallback ∧
              PkgSig bundle fallback pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro fallback ⟨hsame_refl fallback, fallbackUnary, fallbackPkg⟩
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
      exact Or.inr (Or.inr (Or.inl sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, localProvenanceFallback, fallbackPkg⟩
  }
  exact ⟨cert, fallbackUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp.CandidateFrontierRefusalTightening
