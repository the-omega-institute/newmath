import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditClosedTermBudgetTotality [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName closedRead budgetRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg ->
      Cont audit replay closedRead ->
        Cont closedRead ledger budgetRead ->
          Cont budgetRead provenance named ->
            PkgSig bundle named pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                      hsame row closedRead ∨ hsame row ledger ∨
                        hsame row budgetRead ∨ hsame row provenance ∨
                          hsame row named)
                  (fun row : BHist =>
                    hsame row named ∧ Cont frontier sn audit ∧
                      Cont audit replay closedRead ∧
                        Cont closedRead ledger budgetRead ∧
                          PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory audit ∧ UnaryHistory closedRead ∧
                  UnaryHistory budgetRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier auditReplayClosed closedLedgerBudget budgetProvenanceNamed namedPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, _confluenceUnary,
    _auditUnary, ledgerUnary, _transportUnary, replayUnary, provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have closedReadUnary : UnaryHistory closedRead :=
    unary_cont_closed auditUnary replayUnary auditReplayClosed
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed closedReadUnary ledgerUnary closedLedgerBudget
  have namedUnary : UnaryHistory named :=
    unary_cont_closed budgetReadUnary provenanceUnary budgetProvenanceNamed
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
              hsame row closedRead ∨ hsame row ledger ∨ hsame row budgetRead ∨
                hsame row provenance ∨ hsame row named)
          (fun row : BHist =>
            hsame row named ∧ Cont frontier sn audit ∧
              Cont audit replay closedRead ∧ Cont closedRead ledger budgetRead ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named
        ⟨hsame_refl named, namedUnary, namedPkg⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, frontierSnAudit, auditReplayClosed, closedLedgerBudget,
          provenancePkg⟩
  }
  exact ⟨cert, auditUnary, closedReadUnary, budgetReadUnary, namedUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
