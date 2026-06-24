import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.DeciderBoundary

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffDeciderRowExhaustion
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName candidateRead endpointRead deciderRead exhaustedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg ->
      Cont audit candidate candidateRead ->
        Cont candidateRead normalEndpoint endpointRead ->
          Cont endpointRead decidability deciderRead ->
            Cont deciderRead blocked exhaustedRead ->
              PkgSig bundle exhaustedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row exhaustedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidate ∨ hsame row normalEndpoint ∨
                        hsame row decidability ∨ hsame row blocked ∨
                          hsame row deciderRead ∨ hsame row exhaustedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont audit candidate candidateRead ∧
                        Cont candidateRead normalEndpoint endpointRead ∧
                          Cont endpointRead decidability deciderRead ∧
                            Cont deciderRead blocked exhaustedRead ∧
                              PkgSig bundle exhaustedRead pkg)
                    hsame ∧
                  UnaryHistory deciderRead ∧ UnaryHistory exhaustedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier auditCandidateRoute candidateEndpointRoute endpointDeciderRoute
    deciderBlockedRoute exhaustedPkg
  obtain ⟨auditUnary, candidateUnary, normalEndpointUnary, _frontierUnary,
    _confluenceUnary, decidabilityUnary, blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed candidateReadUnary normalEndpointUnary candidateEndpointRoute
  have deciderReadUnary : UnaryHistory deciderRead :=
    unary_cont_closed endpointReadUnary decidabilityUnary endpointDeciderRoute
  have exhaustedReadUnary : UnaryHistory exhaustedRead :=
    unary_cont_closed deciderReadUnary blockedUnary deciderBlockedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exhaustedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row decidability ∨
              hsame row blocked ∨ hsame row deciderRead ∨ hsame row exhaustedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit candidate candidateRead ∧
              Cont candidateRead normalEndpoint endpointRead ∧
                Cont endpointRead decidability deciderRead ∧
                  Cont deciderRead blocked exhaustedRead ∧ PkgSig bundle exhaustedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro exhaustedRead ⟨hsame_refl exhaustedRead, exhaustedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, auditCandidateRoute, candidateEndpointRoute, endpointDeciderRoute,
          deciderBlockedRoute, exhaustedPkg⟩
  }
  exact ⟨cert, deciderReadUnary, exhaustedReadUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
