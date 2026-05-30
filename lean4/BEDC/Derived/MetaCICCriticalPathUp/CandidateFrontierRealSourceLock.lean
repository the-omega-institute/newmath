import BEDC.Derived.MetaCICCriticalPathUp.OpenPhaseConsumerTotality
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateFrontierRealSourceLock [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation realSeal frontier →
        Cont frontier handoff realRead →
          PkgSig bundle realRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row frontier ∨ hsame row realRead ∨ hsame row realSeal) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row frontier ∨ hsame row realRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle realRead pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory frontier ∧ UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledger continuationRealSealFrontier frontierHandoffRealRead realReadPkg
  obtain ⟨packet, dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary realSealUnary continuationRealSealFrontier
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed frontierUnary handoffUnary frontierHandoffRealRead
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row frontier ∨ hsame row realRead ∨ hsame row realSeal) ∧
          UnaryHistory row) frontier := by
    exact ⟨Or.inl (hsame_refl frontier), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontier ∨ hsame row realRead ∨ hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row frontier ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontier sourceFrontier
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
        intro row other sameRows source
        have otherUnary : UnaryHistory other := unary_transport source.right sameRows
        have otherSource :
            hsame other frontier ∨ hsame other realRead ∨ hsame other realSeal := by
          cases source.left with
          | inl sameFrontier =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
          | inr rest =>
              cases rest with
              | inl sameRealRead =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRealRead))
              | inr sameRealSeal =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameRealSeal))
        exact ⟨otherSource, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFrontier))))
      | inr rest =>
          cases rest with
          | inl sameRealRead =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameRealRead))))
          | inr sameRealSeal =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameRealSeal)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realReadPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, realReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
