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

theorem MetaCICCriticalPathPacket_candidate_mediated_sn_frontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        PkgSig bundle frontier pkg →
          SemanticNameCert
              (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                    hsame row continuation ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row regseq ∨ hsame row realSeal ∨ hsame row frontier)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle frontier pkg ∧ PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory frontier ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierPkg
  obtain ⟨packet, dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row frontier ∧ UnaryHistory row) frontier := by
    exact ⟨hsame_refl frontier, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                hsame row continuation ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row realSeal ∨ hsame row frontier)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontier sourceFrontier
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, realSealPkg⟩

theorem MetaCICCriticalPathCandidateMediatedFrontierSocketSeparation [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont unblock obstruction socketRead →
          PkgSig bundle frontier pkg →
            SemanticNameCert
                (fun row : BHist => (hsame row frontier ∨ hsame row socketRead) ∧
                  UnaryHistory row)
                (fun row : BHist =>
                  hsame row obstruction ∨ hsame row discharge ∨ hsame row frontier ∨
                    hsame row socketRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
                    Cont unblock obstruction socketRead)
                hsame ∧
              UnaryHistory frontier ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier unblockObstructionRead frontierPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed unblockUnary obstructionUnary unblockObstructionRead
  have sourceFrontier :
      (fun row : BHist => (hsame row frontier ∨ hsame row socketRead) ∧
        UnaryHistory row) frontier := by
    exact ⟨Or.inl (hsame_refl frontier), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row frontier ∨ hsame row socketRead) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row discharge ∨ hsame row frontier ∨
              hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
              Cont unblock obstruction socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontier sourceFrontier
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        constructor
        · cases source.left with
          | inl sameFrontier =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
          | inr sameSocket =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSocket)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inl sameFrontier))
      | inr sameSocket =>
          exact Or.inr (Or.inr (Or.inr sameSocket))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, unblockObstructionRead⟩
  }
  exact ⟨cert, frontierUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
