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

theorem MetaCICCriticalPathLeanHandoffSurface [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName openNode readyRank downstreamRank obstructionLedger replayRead
      leanHandoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg →
        Cont openNode readyRank leanHandoff →
          PkgSig bundle leanHandoff pkg →
            SemanticNameCert
                (fun row : BHist => hsame row leanHandoff ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                    hsame row obstructionLedger ∨ hsame row replayRead ∨
                      hsame row provenance ∨ hsame row localName ∨ hsame row leanHandoff)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle leanHandoff pkg ∧
                    PkgSig bundle provenance pkg ∧ Cont openNode readyRank leanHandoff)
                hsame ∧
              UnaryHistory leanHandoff := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _packet frontierRank openReadyLean leanPkg
  obtain ⟨openUnary, readyUnary, _downstreamUnary, _obstructionUnary, _replayUnary,
    provenanceUnary, _localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have leanUnary : UnaryHistory leanHandoff :=
    unary_cont_closed openUnary readyUnary openReadyLean
  have sourceLean :
      (fun row : BHist => hsame row leanHandoff ∧ UnaryHistory row) leanHandoff := by
    exact ⟨hsame_refl leanHandoff, leanUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row leanHandoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row leanHandoff)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle leanHandoff pkg ∧
              PkgSig bundle provenance pkg ∧ Cont openNode readyRank leanHandoff)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro leanHandoff sourceLean
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, leanPkg, provenancePkg, openReadyLean⟩
  }
  exact ⟨cert, leanUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
