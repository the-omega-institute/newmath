import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateBoundary [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance localName
      candidateRead projectionRead scopeRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger transport
        replay provenance localName bundle pkg →
      Cont kernel frontier candidateRead →
        Cont candidateRead audit projectionRead →
          Cont projectionRead sn scopeRead →
            Cont scopeRead confluence boundaryRead →
              PkgSig bundle boundaryRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row kernel ∨ hsame row frontier ∨ hsame row audit ∨
                        hsame row sn ∨ hsame row confluence ∨ hsame row candidateRead ∨
                          hsame row projectionRead ∨ hsame row scopeRead ∨
                            hsame row boundaryRead ∨ hsame row provenance)
                    (fun row : BHist =>
                      hsame row boundaryRead ∧ Cont kernel frontier candidateRead ∧
                        Cont candidateRead audit projectionRead ∧
                          Cont projectionRead sn scopeRead ∧
                            Cont scopeRead confluence boundaryRead ∧
                              PkgSig bundle provenance pkg)
                    hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory projectionRead ∧
                  UnaryHistory scopeRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier candidateRoute projectionRoute scopeRoute boundaryRoute _boundaryPkg
  obtain ⟨kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    auditUnary, _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed kernelUnary frontierUnary candidateRoute
  have projectionUnary : UnaryHistory projectionRead :=
    unary_cont_closed candidateUnary auditUnary projectionRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed projectionUnary snUnary scopeRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed scopeUnary confluenceUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row kernel ∨ hsame row frontier ∨ hsame row audit ∨ hsame row sn ∨
              hsame row confluence ∨ hsame row candidateRead ∨ hsame row projectionRead ∨
                hsame row scopeRead ∨ hsame row boundaryRead ∨ hsame row provenance)
          (fun row : BHist =>
            hsame row boundaryRead ∧ Cont kernel frontier candidateRead ∧
              Cont candidateRead audit projectionRead ∧ Cont projectionRead sn scopeRead ∧
                Cont scopeRead confluence boundaryRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead
        ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, candidateRoute, projectionRoute, scopeRoute, boundaryRoute,
          provenancePkg⟩
  }
  exact ⟨cert, candidateUnary, projectionUnary, scopeUnary, boundaryUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp
