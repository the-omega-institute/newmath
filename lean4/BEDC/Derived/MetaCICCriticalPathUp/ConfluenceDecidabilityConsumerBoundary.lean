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

theorem MetaCICCriticalPathConfluenceDecidabilityConsumerBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont handoff localName handoffRead →
          PkgSig bundle frontier pkg →
            PkgSig bundle handoffRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row frontier ∨ hsame row handoffRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row handoff ∨ hsame row continuation ∨ hsame row localName ∨
                      hsame row frontier ∨ hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
                      PkgSig bundle handoffRead pkg ∧ PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory frontier ∧ UnaryHistory handoffRead ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier handoffLocalRead frontierPkg handoffReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalRead
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row frontier ∨ hsame row handoffRead) ∧ UnaryHistory row) frontier := by
    exact ⟨Or.inl (hsame_refl frontier), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontier ∨ hsame row handoffRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row continuation ∨ hsame row localName ∨
              hsame row frontier ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
              PkgSig bundle handoffRead pkg ∧ PkgSig bundle realSeal pkg)
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
          | inr sameHandoffRead =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameHandoffRead)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameFrontier)))
      | inr sameHandoffRead =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameHandoffRead)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, handoffReadPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, handoffReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
