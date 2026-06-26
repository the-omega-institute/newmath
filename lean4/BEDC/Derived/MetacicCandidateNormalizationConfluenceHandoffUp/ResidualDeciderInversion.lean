import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.DeciderBoundary

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateHandoffResidualDeciderInversion [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName residualRead deciderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg ->
      Cont frontier confluence residualRead ->
        Cont residualRead decidability deciderRead ->
          PkgSig bundle deciderRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row deciderRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row frontier ∨ hsame row confluence ∨ hsame row residualRead ∨
                    hsame row decidability ∨ hsame row deciderRead ∨ hsame row blocked)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont frontier confluence residualRead ∧
                    Cont residualRead decidability deciderRead ∧ PkgSig bundle deciderRead pkg)
                hsame ∧
              UnaryHistory residualRead ∧ UnaryHistory deciderRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier frontierConfluenceRoute residualDeciderRoute deciderPkg
  obtain ⟨_auditUnary, _candidateUnary, _normalEndpointUnary, frontierUnary,
    confluenceUnary, decidabilityUnary, blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary confluenceUnary frontierConfluenceRoute
  have deciderReadUnary : UnaryHistory deciderRead :=
    unary_cont_closed residualReadUnary decidabilityUnary residualDeciderRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row deciderRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row confluence ∨ hsame row residualRead ∨
              hsame row decidability ∨ hsame row deciderRead ∨ hsame row blocked)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont frontier confluence residualRead ∧
              Cont residualRead decidability deciderRead ∧ PkgSig bundle deciderRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro deciderRead ⟨hsame_refl deciderRead, deciderReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, frontierConfluenceRoute, residualDeciderRoute, deciderPkg⟩
  }
  exact ⟨cert, residualReadUnary, deciderReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
