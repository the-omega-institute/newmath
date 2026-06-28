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

theorem MetacicCandidateNormalizationConfluenceHandoffCandidateRowReadiness
    [AskSetup] [PackageSetup]
    {audit candidate normalEndpoint frontier confluence decidability blocked transport replay
      provenance localName candidateRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffCarrier audit candidate
        normalEndpoint frontier confluence decidability blocked transport replay provenance
        localName bundle pkg ->
      Cont audit candidate candidateRead ->
        Cont candidateRead frontier frontierRead ->
          PkgSig bundle frontierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row audit ∨ hsame row candidate ∨ hsame row candidateRead ∨
                    hsame row frontier ∨ hsame row frontierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont audit candidate candidateRead ∧
                    Cont candidateRead frontier frontierRead ∧ PkgSig bundle frontierRead pkg)
                hsame ∧ UnaryHistory candidateRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditCandidateRoute candidateFrontierRoute frontierPkg
  obtain ⟨auditUnary, candidateUnary, _normalUnary, frontierUnary, _confluenceUnary,
    _decidabilityUnary, _blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary candidateFrontierRoute
  refine ⟨?_, candidateReadUnary, frontierReadUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨frontierRead, hsame_refl frontierRead, frontierReadUnary⟩
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
    exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
      unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
  · intro _row sourceRow
    exact ⟨sourceRow.right, auditCandidateRoute, candidateFrontierRoute, frontierPkg⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp
