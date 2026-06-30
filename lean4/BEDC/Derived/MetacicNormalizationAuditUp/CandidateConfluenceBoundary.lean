import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateConfluenceBoundary [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      candidateRead closedRead residualRead socketRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg ->
      Cont frontier sn candidateRead ->
        Cont candidateRead audit closedRead ->
          Cont closedRead replay residualRead ->
            Cont residualRead confluence socketRead ->
              Cont socketRead localName boundaryRead ->
                PkgSig bundle boundaryRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row boundaryRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row closedRead ∨
                          hsame row residualRead ∨ hsame row socketRead ∨
                            hsame row boundaryRead ∨ hsame row localName ∨
                              hsame row provenance)
                      (fun row : BHist =>
                        hsame row boundaryRead ∧ Cont residualRead confluence socketRead ∧
                          Cont socketRead localName boundaryRead ∧
                            PkgSig bundle provenance pkg)
                      hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory closedRead ∧
                    UnaryHistory residualRead ∧ UnaryHistory socketRead ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: MetacicNormalizationAuditUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frontierSnCandidate candidateAuditClosed closedReplayResidual
    residualConfluenceSocket socketLocalBoundary boundaryPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed frontierUnary snUnary frontierSnCandidate
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed candidateUnary auditUnary candidateAuditClosed
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed closedUnary replayUnary closedReplayResidual
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary confluenceUnary residualConfluenceSocket
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed socketUnary localNameUnary socketLocalBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row boundaryRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row closedRead ∨ hsame row residualRead ∨
              hsame row socketRead ∨ hsame row boundaryRead ∨ hsame row localName ∨
                hsame row provenance)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont residualRead confluence socketRead ∧
              Cont socketRead localName boundaryRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead
        ⟨hsame_refl boundaryRead, boundaryUnary, boundaryPkg⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, residualConfluenceSocket, socketLocalBoundary, provenancePkg⟩
  }
  exact ⟨cert, candidateUnary, closedUnary, residualUnary, socketUnary, boundaryUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
