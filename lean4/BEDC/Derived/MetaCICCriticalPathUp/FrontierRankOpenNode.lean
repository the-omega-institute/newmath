import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICCriticalPathFrontierRankCarrier [AskSetup] [PackageSetup]
    (openNode readyRank downstreamRank obstructionLedger replayRead provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory openNode ∧ UnaryHistory readyRank ∧ UnaryHistory downstreamRank ∧
    UnaryHistory obstructionLedger ∧ UnaryHistory replayRead ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont openNode readyRank downstreamRank ∧
        Cont obstructionLedger replayRead localName ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem MetaCICCriticalPathFrontierRank_open_node_exhaustion
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName openNode readyRank downstreamRank obstructionLedger replayRead
      frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg ->
        Cont openNode readyRank frontierRead ->
          PkgSig bundle frontierRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                    hsame row obstructionLedger ∨ hsame row replayRead ∨
                      hsame row frontierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                    PkgSig bundle provenance pkg ∧ Cont openNode readyRank frontierRead)
                hsame ∧
              UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro _packet frontierRank openReadyFrontier frontierPkg
  obtain ⟨openUnary, readyUnary, _downstreamUnary, _obstructionUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed openUnary readyUnary openReadyFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row) frontierRead := by
    exact ⟨hsame_refl frontierRead, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨
                hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle provenance pkg ∧ Cont openNode readyRank frontierRead)
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, provenancePkg, openReadyFrontier⟩
  }
  exact ⟨cert, frontierUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
