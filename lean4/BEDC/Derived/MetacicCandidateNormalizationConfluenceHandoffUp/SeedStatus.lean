import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffSeedStatus [AskSetup] [PackageSetup]
    {A K N F C D B T R P L seedRead frontierRead residualRead deciderRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P
        L bundle pkg ->
      Cont A K seedRead ->
        Cont seedRead F frontierRead ->
          Cont frontierRead C residualRead ->
            Cont residualRead D deciderRead ->
              PkgSig bundle deciderRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row deciderRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨
                        hsame row B ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨
                          hsame row L ∨ hsame row deciderRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont seedRead F frontierRead ∧
                        Cont frontierRead C residualRead ∧ Cont residualRead D deciderRead ∧
                          PkgSig bundle deciderRead pkg)
                    hsame ∧
                  UnaryHistory seedRead ∧
                    UnaryHistory frontierRead ∧
                      UnaryHistory residualRead ∧ UnaryHistory deciderRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditCandidateRoute seedFrontierRoute frontierResidualRoute
    residualDeciderRoute deciderPkg
  obtain ⟨auditUnary, candidateUnary, _normalEndpointUnary, frontierUnary,
    confluenceUnary, decidabilityUnary, _blockedUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkg⟩ := carrier
  have seedReadUnary : UnaryHistory seedRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed seedReadUnary frontierUnary seedFrontierRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierReadUnary confluenceUnary frontierResidualRoute
  have deciderReadUnary : UnaryHistory deciderRead :=
    unary_cont_closed residualReadUnary decidabilityUnary residualDeciderRoute
  refine ⟨?_, seedReadUnary, frontierReadUnary, residualReadUnary, deciderReadUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨deciderRead, hsame_refl deciderRead, deciderReadUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows sourceRow
    exact
      ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
        unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr sourceRow.left))))))))
  · intro _row sourceRow
    exact
      ⟨sourceRow.right, seedFrontierRoute, frontierResidualRoute, residualDeciderRoute,
        deciderPkg⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
