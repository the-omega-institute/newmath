import BEDC.Derived.MetaCICCriticalPathUp.FrontierRankOpenNode
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathFrontierRank_consumer_exactness [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg →
      Cont downstreamRank replayRead consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row consumer)
              (fun row : BHist =>
                hsame row consumer ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank downstreamReplayConsumer consumerPkg
  obtain ⟨_openUnary, _readyUnary, downstreamUnary, _obstructionUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary replayUnary downstreamReplayConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row consumer)
          (fun row : BHist =>
            hsame row consumer ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer sourceConsumer
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
      exact ⟨source.left, provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
