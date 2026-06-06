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

theorem MetaCICCriticalPathFrontierRankSoundness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName openNode readyRank downstreamRank obstructionLedger replayRead frontierRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg ->
        Cont openNode readyRank frontierRead ->
          Cont downstreamRank replayRead consumer ->
            PkgSig bundle frontierRead pkg ->
              PkgSig bundle consumer pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row frontierRead ∨ hsame row consumer) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row openNode ∨ hsame row readyRank ∨
                        hsame row downstreamRank ∨ hsame row obstructionLedger ∨
                          hsame row replayRead ∨ hsame row frontierRead ∨
                            hsame row consumer)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                        PkgSig bundle consumer pkg ∧ PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory frontierRead ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _packet frontierRank openReadyFrontier downstreamReplayConsumer frontierPkg consumerPkg
  obtain ⟨openUnary, readyUnary, downstreamUnary, _obstructionUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed openUnary readyUnary openReadyFrontier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary replayUnary downstreamReplayConsumer
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row frontierRead ∨ hsame row consumer) ∧ UnaryHistory row)
          frontierRead := by
    exact ⟨Or.inl (hsame_refl frontierRead), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontierRead ∨ hsame row consumer) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row frontierRead ∨
                hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle consumer pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead sourceFrontier
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
        constructor
        · cases source.left with
          | inl sameFrontier =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
          | inr sameConsumer =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameConsumer)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFrontier)))))
      | inr sameConsumer =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameConsumer)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, consumerPkg, provenancePkg⟩
  }
  exact ⟨cert, frontierUnary, consumerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
