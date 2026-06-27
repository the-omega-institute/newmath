import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffParallelDiamondForwardLink
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName candidateRead frontierRead confluenceRead decidableRead blockedRead
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint frontier
        confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont audit candidate candidateRead →
        Cont candidateRead frontier frontierRead →
          Cont frontierRead confluence confluenceRead →
            Cont confluenceRead decidability decidableRead →
              Cont decidableRead blocked blockedRead →
                Cont blockedRead normalEndpoint endpointRead →
                  PkgSig bundle endpointRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidate ∨ hsame row frontier ∨
                            hsame row confluence ∨ hsame row decidability ∨
                              hsame row blocked ∨ hsame row normalEndpoint ∨
                                hsame row endpointRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont audit candidate candidateRead ∧
                            Cont candidateRead frontier frontierRead ∧
                              Cont frontierRead confluence confluenceRead ∧
                                Cont confluenceRead decidability decidableRead ∧
                                  Cont decidableRead blocked blockedRead ∧
                                    Cont blockedRead normalEndpoint endpointRead ∧
                                      PkgSig bundle endpointRead pkg)
                        hsame ∧
                      UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                        UnaryHistory confluenceRead ∧ UnaryHistory decidableRead ∧
                          UnaryHistory blockedRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: MetacicCandidateNormalizationConfluenceHandoffCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier candidateRoute frontierRoute confluenceRoute decidableRoute blockedRoute
    endpointRoute endpointPkg
  obtain ⟨auditUnary, candidateUnary, normalEndpointUnary, frontierUnary, confluenceUnary,
    decidabilityUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary candidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary frontierRoute
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed frontierReadUnary confluenceUnary confluenceRoute
  have decidableReadUnary : UnaryHistory decidableRead :=
    unary_cont_closed confluenceReadUnary decidabilityUnary decidableRoute
  have blockedReadUnary : UnaryHistory blockedRead :=
    unary_cont_closed decidableReadUnary blockedUnary blockedRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed blockedReadUnary normalEndpointUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row frontier ∨ hsame row confluence ∨
              hsame row decidability ∨ hsame row blocked ∨ hsame row normalEndpoint ∨
                hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit candidate candidateRead ∧
              Cont candidateRead frontier frontierRead ∧
                Cont frontierRead confluence confluenceRead ∧
                  Cont confluenceRead decidability decidableRead ∧
                    Cont decidableRead blocked blockedRead ∧
                      Cont blockedRead normalEndpoint endpointRead ∧
                        PkgSig bundle endpointRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, candidateRoute, frontierRoute, confluenceRoute, decidableRoute,
          blockedRoute, endpointRoute, endpointPkg⟩
  }
  exact
    ⟨cert, candidateReadUnary, frontierReadUnary, confluenceReadUnary, decidableReadUnary,
      blockedReadUnary, endpointReadUnary⟩

end BEDC.Derived
