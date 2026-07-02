import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffVisionConcretization
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName auditRead endpointRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg ->
      Cont audit candidate auditRead ->
        Cont candidate normalEndpoint endpointRead ->
          Cont endpointRead confluence publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
                      hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                        hsame row blocked ∨ hsame row transport ∨ hsame row replay ∨
                          hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont audit candidate auditRead ∧
                      Cont candidate normalEndpoint endpointRead ∧
                        Cont endpointRead confluence publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame ∧ UnaryHistory auditRead ∧ UnaryHistory endpointRead ∧
                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier auditRoute endpointRoute publicRoute publicPkg
  obtain ⟨auditUnary, candidateUnary, normalEndpointUnary, _frontierUnary,
    confluenceUnary, _decidabilityUnary, _blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed auditUnary candidateUnary auditRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateUnary normalEndpointUnary endpointRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointReadUnary confluenceUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row audit ∨ hsame row candidate ∨ hsame row normalEndpoint ∨
              hsame row frontier ∨ hsame row confluence ∨ hsame row decidability ∨
                hsame row blocked ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit candidate auditRead ∧
              Cont candidate normalEndpoint endpointRead ∧
                Cont endpointRead confluence publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := by
    refine
      { core :=
          { carrier_inhabited := ?_
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · exact ⟨publicRead, hsame_refl publicRead, publicReadUnary⟩
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows source
      exact
        ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    · intro _row source
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
                            (Or.inr source.left))))))))))
    · intro _row source
      exact ⟨source.right, auditRoute, endpointRoute, publicRoute, publicPkg⟩
  exact ⟨cert, auditReadUnary, endpointReadUnary, publicReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
