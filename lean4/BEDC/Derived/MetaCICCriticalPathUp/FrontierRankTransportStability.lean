import BEDC.Derived.MetaCICCriticalPathUp.FrontierRankNameCertObligations

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathFrontierRank_transport_stability [AskSetup] [PackageSetup]
    {openNode readyRank downstreamRank obstructionLedger replayRead provenance localName
      transportedLocal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathFrontierRankCarrier openNode readyRank downstreamRank
        obstructionLedger replayRead provenance localName bundle pkg ->
      hsame transportedLocal localName ->
        PkgSig bundle transportedLocal pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row transportedLocal ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
                  hsame row obstructionLedger ∨ hsame row replayRead ∨
                    hsame row transportedLocal)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle transportedLocal pkg)
              hsame ∧
            UnaryHistory transportedLocal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro frontierRank sameTransported transportedPkg
  obtain ⟨_openUnary, _readyUnary, _downstreamUnary, _obstructionUnary, _replayUnary,
    _provenanceUnary, localNameUnary, _openReadyDownstream, _obstructionReplayLocal,
    provenancePkg, _localNamePkg⟩ := frontierRank
  have transportedUnary : UnaryHistory transportedLocal :=
    unary_transport localNameUnary (hsame_symm sameTransported)
  have sourceTransported :
      (fun row : BHist => hsame row transportedLocal ∧ UnaryHistory row)
          transportedLocal := by
    exact ⟨hsame_refl transportedLocal, transportedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedLocal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row openNode ∨ hsame row readyRank ∨ hsame row downstreamRank ∨
              hsame row obstructionLedger ∨ hsame row replayRead ∨
                hsame row transportedLocal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle transportedLocal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro transportedLocal sourceTransported
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
      exact ⟨source.right, provenancePkg, transportedPkg⟩
  }
  exact ⟨cert, transportedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
