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

theorem MetaCICCriticalPathCandidateMediatedSNDischargeRow [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont obstruction discharge dischargeRead →
          PkgSig bundle frontier pkg →
            PkgSig bundle dischargeRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row frontier ∨ hsame row dischargeRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row obstruction ∨ hsame row discharge ∨ hsame row frontier ∨
                      hsame row dischargeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
                      PkgSig bundle dischargeRead pkg ∧ PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory frontier ∧ UnaryHistory dischargeRead ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier obstructionDischargeRead frontierPkg dischargeReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed obstructionUnary dischargeUnary obstructionDischargeRead
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row frontier ∨ hsame row dischargeRead) ∧ UnaryHistory row) frontier := by
    exact ⟨Or.inl (hsame_refl frontier), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontier ∨ hsame row dischargeRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row discharge ∨ hsame row frontier ∨
              hsame row dischargeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
              PkgSig bundle dischargeRead pkg ∧ PkgSig bundle realSeal pkg)
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
          | inr sameDischarge =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameDischarge)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inl sameFrontier))
      | inr sameDischarge =>
          exact Or.inr (Or.inr (Or.inr sameDischarge))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, dischargeReadPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, dischargeReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
