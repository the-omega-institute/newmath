import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.NormalEndpointReadback

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffNormalEndpointRetention
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg ->
      Cont candidate normalEndpoint endpointRead ->
        PkgSig bundle endpointRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row endpointRead ∨
                  hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                    hsame row blocked)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
              hsame ∧
            UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier endpointRoute endpointPkg
  obtain ⟨_auditUnary, candidateUnary, normalEndpointUnary, _frontierUnary,
    _confluenceUnary, _decidabilityUnary, _blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateUnary normalEndpointUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row endpointRead ∨
              hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                hsame row blocked)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpointRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }
  exact ⟨cert, endpointReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
