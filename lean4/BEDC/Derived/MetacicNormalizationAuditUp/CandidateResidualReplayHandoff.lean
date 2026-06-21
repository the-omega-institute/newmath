import BEDC.Derived.MetacicNormalizationAuditUp

namespace BEDC.Derived.MetacicNormalizationAuditUp.CandidateResidualReplayHandoff

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicNormalizationAuditCandidateResidualReplayHandoff [AskSetup] [PackageSetup]
    {kernel normalizer frontier sn confluence audit ledger transport replay provenance
      localName candidateRead residualRead socketRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicNormalizationAuditUp kernel normalizer frontier sn confluence audit ledger
        transport replay provenance localName bundle pkg →
      Cont frontier sn candidateRead →
        Cont candidateRead replay residualRead →
          Cont residualRead confluence socketRead →
            Cont socketRead localName publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row residualRead ∨
                        hsame row socketRead ∨ hsame row publicRead ∨
                          hsame row provenance)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont candidateRead replay residualRead ∧
                        Cont residualRead confluence socketRead ∧
                          Cont socketRead localName publicRead ∧
                            PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory socketRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory PkgSig
  intro carrier candidateRoute residualRoute socketRoute publicRoute publicPkg
  obtain ⟨_kernelUnary, _normalizerUnary, frontierUnary, snUnary, confluenceUnary,
    _auditUnary, _ledgerUnary, _transportUnary, replayUnary, _provenanceUnary,
    localNameUnary, _kernelNormalizerFrontier, _frontierSnAudit, _confluenceAuditLedger,
    _transportReplaySame, _provenancePkg, _localNamePkg⟩ := carrier
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed frontierUnary snUnary candidateRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary replayUnary residualRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary confluenceUnary socketRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed socketUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
              hsame row publicRead ∨ hsame row provenance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidateRead replay residualRead ∧
              Cont residualRead confluence socketRead ∧ Cont socketRead localName publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        ⟨hsame_refl publicRead, publicUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, residualRoute, socketRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, socketUnary, publicUnary⟩

end BEDC.Derived.MetacicNormalizationAuditUp.CandidateResidualReplayHandoff
