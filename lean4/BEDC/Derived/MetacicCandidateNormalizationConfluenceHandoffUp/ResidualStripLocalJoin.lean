import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffResidualStripLocalJoin
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName residualRead localJoinRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate normalEndpoint
        frontier confluence decidability blocked transport replay provenance localName bundle pkg →
      Cont candidate confluence residualRead →
        Cont residualRead blocked localJoinRead →
          PkgSig bundle localJoinRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row localJoinRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row candidate ∨ hsame row normalEndpoint ∨ hsame row confluence ∨
                    hsame row decidability ∨ hsame row blocked ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row provenance ∨ hsame row localName ∨
                        hsame row localJoinRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle localJoinRead pkg ∧
                    Cont candidate confluence residualRead ∧
                      Cont residualRead blocked localJoinRead)
                hsame ∧
              UnaryHistory residualRead ∧ UnaryHistory localJoinRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier candidateConfluenceRoute residualBlockedRoute localJoinPkg
  obtain ⟨_auditUnary, candidateUnary, _normalUnary, _frontierUnary, confluenceUnary,
    _decidableUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary confluenceUnary candidateConfluenceRoute
  have localJoinUnary : UnaryHistory localJoinRead :=
    unary_cont_closed residualUnary blockedUnary residualBlockedRoute
  refine ⟨?_, residualUnary, localJoinUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨localJoinRead, hsame_refl localJoinRead, localJoinUnary⟩
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
      ⟨sourceRow.right, localJoinPkg, candidateConfluenceRoute, residualBlockedRoute⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
