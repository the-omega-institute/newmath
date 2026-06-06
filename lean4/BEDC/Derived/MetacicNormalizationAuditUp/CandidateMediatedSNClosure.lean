import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateMediatedSNClosure [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      appRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont audit replay appRead ->
        Cont appRead ledger ledgerRead ->
          PkgSig bundle ledgerRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                  hsame row appRead ∨ hsame row ledgerRead ∨ hsame row provenance)
              (fun row : BHist =>
                hsame row ledgerRead ∧ Cont frontier sn audit ∧
                  Cont audit replay appRead ∧ Cont appRead ledger ledgerRead ∧
                    PkgSig bundle provenance pkg)
              hsame ∧ UnaryHistory audit ∧ UnaryHistory appRead ∧
                UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier appRoute ledgerRoute ledgerPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have appUnary : UnaryHistory appRead :=
    unary_cont_closed auditUnary replayUnary appRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed appUnary ledgerUnary ledgerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨ hsame row appRead ∨
            hsame row ledgerRead ∨ hsame row provenance)
        (fun row : BHist =>
          hsame row ledgerRead ∧ Cont frontier sn audit ∧ Cont audit replay appRead ∧
            Cont appRead ledger ledgerRead ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead
        ⟨hsame_refl ledgerRead, ledgerReadUnary, ledgerPkg⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, frontierSnAudit, appRoute, ledgerRoute, provenancePkg⟩
  }
  exact ⟨cert, auditUnary, appUnary, ledgerReadUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
