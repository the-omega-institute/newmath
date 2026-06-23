import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffConsumerBoundary
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName publicRead frontierRead residualRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg ->
      Cont audit candidate publicRead ->
        Cont publicRead frontier frontierRead ->
          Cont frontierRead confluence residualRead ->
            PkgSig bundle publicRead pkg ->
              PkgSig bundle residualRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
                        hsame row frontier ∨ hsame row confluence ∨
                          hsame row decidability ∨ hsame row blocked ∨
                            hsame row transport ∨ hsame row replay ∨
                              hsame row provenance ∨ hsame row localName ∨
                                hsame row publicRead ∨ hsame row frontierRead ∨
                                  hsame row residualRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont audit candidate publicRead ∧
                        Cont publicRead frontier frontierRead ∧
                          Cont frontierRead confluence residualRead ∧
                            PkgSig bundle residualRead pkg)
                    hsame ∧
                  UnaryHistory publicRead ∧ UnaryHistory frontierRead ∧
                    UnaryHistory residualRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier auditCandidateRoute publicFrontierRoute frontierConfluenceRoute _publicPkg
    residualPkg
  obtain ⟨auditUnary, candidateUnary, _normalUnary, frontierUnary, confluenceUnary,
    _decidabilityUnary, _blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed publicUnary frontierUnary publicFrontierRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierReadUnary confluenceUnary frontierConfluenceRoute
  have sourceAtResidual :
      (fun row : BHist => hsame row residualRead ∧ UnaryHistory row) residualRead := by
    exact ⟨hsame_refl residualRead, residualUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row residualRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
              hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                hsame row blocked ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row publicRead ∨
                    hsame row frontierRead ∨ hsame row residualRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit candidate publicRead ∧
              Cont publicRead frontier frontierRead ∧
                Cont frontierRead confluence residualRead ∧ PkgSig bundle residualRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro residualRead sourceAtResidual
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, auditCandidateRoute, publicFrontierRoute, frontierConfluenceRoute,
          residualPkg⟩
  }
  exact ⟨cert, publicUnary, frontierReadUnary, residualUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
