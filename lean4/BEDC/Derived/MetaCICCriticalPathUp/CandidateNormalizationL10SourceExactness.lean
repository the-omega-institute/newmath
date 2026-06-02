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

theorem MetaCICCriticalPathCandidateNormalizationL10SourceExactness
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont dyadic stream l10Read →
          PkgSig bundle frontier pkg →
            PkgSig bundle l10Read pkg →
              SemanticNameCert
                  (fun row : BHist => (hsame row frontier ∨ hsame row l10Read) ∧
                    UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row frontier ∨ hsame row l10Read)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
                      PkgSig bundle realSeal pkg ∧ PkgSig bundle l10Read pkg)
                  hsame ∧
                UnaryHistory frontier ∧ UnaryHistory l10Read ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier dyadicStreamL10 frontierPkg l10Pkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamL10
  have sourceFrontier :
      (fun row : BHist => (hsame row frontier ∨ hsame row l10Read) ∧
        UnaryHistory row) frontier := by
    exact ⟨Or.inl (hsame_refl frontier), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row frontier ∨ hsame row l10Read) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row frontier ∨ hsame row l10Read)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧ PkgSig bundle realSeal pkg ∧
              PkgSig bundle l10Read pkg)
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
        intro _row _other sameRows source
        constructor
        · cases source.left with
          | inl sameFrontier =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
          | inr sameL10 =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameL10)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFrontier))))
      | inr sameL10 =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameL10))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, realSealPkg, l10Pkg⟩
  }
  exact ⟨cert, frontierUnary, l10Unary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
