import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateFrontierConfluenceSocketBoundary [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier confluenceRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation realSeal frontier →
        Cont frontier handoff confluenceRead →
          Cont unblock obstruction socketRead →
            PkgSig bundle confluenceRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row confluenceRead ∨ hsame row socketRead ∨
                        hsame row frontier) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row frontier ∨
                        hsame row confluenceRead ∨ hsame row socketRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
                      Cont unblock obstruction socketRead)
                  hsame ∧
                UnaryHistory confluenceRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationRealFrontier frontierHandoffConfluence unblockObstructionSocket
    confluencePkg
  obtain ⟨packet, dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary realSealUnary continuationRealFrontier
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed frontierUnary handoffUnary frontierHandoffConfluence
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed unblockUnary obstructionUnary unblockObstructionSocket
  have sourceConfluence :
      (fun row : BHist =>
        (hsame row confluenceRead ∨ hsame row socketRead ∨ hsame row frontier) ∧
          UnaryHistory row) confluenceRead := by
    exact ⟨Or.inl (hsame_refl confluenceRead), confluenceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row confluenceRead ∨ hsame row socketRead ∨ hsame row frontier) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row frontier ∨ hsame row confluenceRead ∨
                hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle confluenceRead pkg ∧
              Cont unblock obstruction socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro confluenceRead sourceConfluence
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
          | inl sameConfluence =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameConfluence)
          | inr rest =>
              cases rest with
              | inl sameSocket =>
                  exact Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) sameSocket))
              | inr sameFrontier =>
                  exact Or.inr
                    (Or.inr (hsame_trans (hsame_symm sameRows) sameFrontier))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameConfluence =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameConfluence)))))
      | inr rest =>
          cases rest with
          | inl sameSocket =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSocket)))))
          | inr sameFrontier =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFrontier))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, confluencePkg, unblockObstructionSocket⟩
  }
  exact ⟨cert, confluenceUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
