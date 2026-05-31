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

theorem MetaCICCriticalPathCandidateSNL10DependencySeal [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal normalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation normalForm normalRead →
        PkgSig bundle normalRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row normalRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle normalRead pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory normalRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger continuationNormalRead normalReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed continuationUnary normalFormUnary continuationNormalRead
  have sourceNormalRead :
      (fun row : BHist => hsame row normalRead ∧ UnaryHistory row) normalRead := by
    exact ⟨hsame_refl normalRead, normalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row normalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle normalRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normalRead sourceNormalRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, normalReadPkg, realSealPkg⟩
  }
  exact ⟨cert, normalReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
