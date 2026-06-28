import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationHandoffObligationStability [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName candidateRead endpointRead residualRead deciderRead retainedRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg →
      Cont audit candidate candidateRead →
        Cont candidateRead normalEndpoint endpointRead →
          Cont frontier confluence residualRead →
            Cont endpointRead decidability deciderRead →
              Cont residualRead blocked retainedRead →
                PkgSig bundle retainedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidate ∨ hsame row normalEndpoint ∨
                          hsame row frontier ∨ hsame row confluence ∨
                            hsame row decidability ∨ hsame row blocked ∨
                              hsame row transport ∨ hsame row replay ∨
                                hsame row provenance ∨ hsame row localName ∨
                                  hsame row endpointRead ∨ hsame row residualRead ∨
                                    hsame row deciderRead ∨ hsame row retainedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont audit candidate candidateRead ∧
                          Cont candidateRead normalEndpoint endpointRead ∧
                            Cont frontier confluence residualRead ∧
                              Cont endpointRead decidability deciderRead ∧
                                Cont residualRead blocked retainedRead ∧
                                  PkgSig bundle retainedRead pkg)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory endpointRead ∧
                      UnaryHistory residualRead ∧ UnaryHistory deciderRead ∧
                        UnaryHistory retainedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier auditCandidateRoute candidateEndpointRoute frontierConfluenceRoute
    endpointDeciderRoute residualBlockedRoute retainedPkg
  obtain ⟨auditUnary, candidateUnary, normalEndpointUnary, frontierUnary, confluenceUnary,
    decidabilityUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateReadUnary normalEndpointUnary candidateEndpointRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierUnary confluenceUnary frontierConfluenceRoute
  have deciderReadUnary : UnaryHistory deciderRead :=
    unary_cont_closed endpointReadUnary decidabilityUnary endpointDeciderRoute
  have retainedReadUnary : UnaryHistory retainedRead :=
    unary_cont_closed residualReadUnary blockedUnary residualBlockedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row frontier ∨
              hsame row confluence ∨ hsame row decidability ∨ hsame row blocked ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row endpointRead ∨ hsame row residualRead ∨
                    hsame row deciderRead ∨ hsame row retainedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit candidate candidateRead ∧
              Cont candidateRead normalEndpoint endpointRead ∧
                Cont frontier confluence residualRead ∧
                  Cont endpointRead decidability deciderRead ∧
                    Cont residualRead blocked retainedRead ∧ PkgSig bundle retainedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro retainedRead ⟨hsame_refl retainedRead, retainedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, auditCandidateRoute, candidateEndpointRoute, frontierConfluenceRoute,
          endpointDeciderRoute, residualBlockedRoute, retainedPkg⟩
  }
  exact
    ⟨cert, candidateReadUnary, endpointReadUnary, residualReadUnary, deciderReadUnary,
      retainedReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
