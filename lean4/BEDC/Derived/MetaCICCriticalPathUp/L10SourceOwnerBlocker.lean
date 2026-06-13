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

theorem MetaCICCriticalPathL10SourceOwnerBlocker [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceRead ownerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal sourceRead →
          Cont sourceRead obstruction ownerRead →
            PkgSig bundle ownerRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceRead ∨ hsame row ownerRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row obstruction ∨
                        hsame row sourceRead ∨ hsame row ownerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle ownerRead pkg ∧
                      PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory ownerRead ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger _dyadicStreamRegseq regseqRealSealSource sourceObstructionOwner ownerPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealSource
  have ownerUnary : UnaryHistory ownerRead :=
    unary_cont_closed sourceUnary obstructionUnary sourceObstructionOwner
  have sourceWitness :
      (fun row : BHist =>
        (hsame row sourceRead ∨ hsame row ownerRead) ∧ UnaryHistory row) sourceRead := by
    exact ⟨Or.inl (hsame_refl sourceRead), sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceRead ∨ hsame row ownerRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row obstruction ∨ hsame row sourceRead ∨
                hsame row ownerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle ownerRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceWitness
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
          ⟨by
            cases source.left with
            | inl sourceSame =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sourceSame)
            | inr ownerSame =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) ownerSame),
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sourceSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceSame)))))
      | inr ownerSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ownerSame)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ownerPkg, realSealPkg⟩
  }
  exact ⟨cert, sourceUnary, ownerUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
