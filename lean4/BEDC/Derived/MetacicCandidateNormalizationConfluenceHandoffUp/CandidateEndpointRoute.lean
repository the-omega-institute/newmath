import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.TasteGate

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffCarrier_candidate_endpoint_route
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint
        frontier confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont candidate normalEndpoint endpointRead →
        PkgSig bundle provenance pkg →
          SemanticNameCert
              (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row frontier ∨
                  hsame row blocked ∨ hsame row endpointRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont candidate normalEndpoint endpointRead ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier endpointRoute packageProof
  obtain ⟨_auditUnary, candidateUnary, normalEndpointUnary, _frontierUnary,
    _confluenceUnary, _decidabilityUnary, _blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateUnary normalEndpointUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row frontier ∨
              hsame row blocked ∨ hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidate normalEndpoint endpointRead ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, packageProof⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
