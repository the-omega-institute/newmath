import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateRoutePack [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName closedRead residualRead socketRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg ->
      Cont frontier sn audit ->
        Cont audit replay closedRead ->
          Cont closedRead ledger residualRead ->
            Cont residualRead confluence socketRead ->
              Cont socketRead provenance named ->
                PkgSig bundle named pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                      (fun row : BHist =>
                        hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
                          hsame row closedRead ∨ hsame row residualRead ∨
                            hsame row confluence ∨ hsame row socketRead ∨
                              hsame row provenance ∨ hsame row named)
                      (fun row : BHist =>
                        hsame row named ∧ Cont frontier sn audit ∧
                          Cont audit replay closedRead ∧
                            Cont closedRead ledger residualRead ∧
                              Cont residualRead confluence socketRead ∧
                                PkgSig bundle provenance pkg)
                      hsame ∧ UnaryHistory audit ∧ UnaryHistory closedRead ∧
                    UnaryHistory residualRead ∧ UnaryHistory socketRead ∧
                      UnaryHistory named := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnAudit auditReplayClosed closedLedgerResidual
    residualConfluenceSocket socketProvenanceNamed namedPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    _auditUnary, ledgerUnary, _transportUnary, replayUnary, provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit,
    _confluenceAuditLedger, _transportReplaySame, provenancePkg, _localNamePkg⟩ :=
    carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed frontierUnary snUnary frontierSnAudit
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed auditUnary replayUnary auditReplayClosed
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed closedUnary ledgerUnary closedLedgerResidual
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary confluenceUnary residualConfluenceSocket
  have namedUnary : UnaryHistory named :=
    unary_cont_closed socketUnary provenanceUnary socketProvenanceNamed
  have sourceNamed :
      (fun row : BHist =>
        hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg) named := by
    exact ⟨hsame_refl named, namedUnary, namedPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row named ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row sn ∨ hsame row audit ∨
              hsame row closedRead ∨ hsame row residualRead ∨
                hsame row confluence ∨ hsame row socketRead ∨
                  hsame row provenance ∨ hsame row named)
          (fun row : BHist =>
            hsame row named ∧ Cont frontier sn audit ∧
              Cont audit replay closedRead ∧ Cont closedRead ledger residualRead ∧
                Cont residualRead confluence socketRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named sourceNamed
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, frontierSnAudit, auditReplayClosed, closedLedgerResidual,
          residualConfluenceSocket, provenancePkg⟩
  }
  exact ⟨cert, auditUnary, closedUnary, residualUnary, socketUnary, namedUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
