import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateLedgerLocality [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      residualRead budgetRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont audit replay residualRead ->
        Cont residualRead confluence budgetRead ->
          Cont budgetRead localName ledgerRead ->
            PkgSig bundle ledgerRead pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                    hsame row confluence ∨ hsame row residualRead ∨
                      hsame row budgetRead ∨ hsame row localName ∨
                        hsame row ledgerRead ∨ hsame row provenance)
                (fun row : BHist =>
                  hsame row ledgerRead ∧ Cont frontier sn audit ∧
                    Cont audit replay residualRead ∧
                      Cont residualRead confluence budgetRead ∧
                        Cont budgetRead localName ledgerRead ∧
                          PkgSig bundle provenance pkg)
                hsame ∧ UnaryHistory residualRead ∧ UnaryHistory budgetRead ∧
                  UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier residualRoute budgetRoute ledgerRoute ledgerPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    localNameUnary, _kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed auditUnary replayUnary residualRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed residualUnary confluenceUnary budgetRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed budgetUnary localNameUnary ledgerRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨ hsame row confluence ∨
            hsame row residualRead ∨ hsame row budgetRead ∨ hsame row localName ∨
              hsame row ledgerRead ∨ hsame row provenance)
        (fun row : BHist =>
          hsame row ledgerRead ∧ Cont frontier sn audit ∧
            Cont audit replay residualRead ∧ Cont residualRead confluence budgetRead ∧
              Cont budgetRead localName ledgerRead ∧ PkgSig bundle provenance pkg)
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
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, frontierSnAudit, residualRoute, budgetRoute, ledgerRoute,
          provenancePkg⟩
  }
  exact ⟨cert, residualUnary, budgetUnary, ledgerReadUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
