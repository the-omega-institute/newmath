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

theorem MetaCICCriticalPathFourFaceBoundedCheckerGate [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal checkerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont handoff continuation checkerRead ->
        PkgSig bundle checkerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                    hsame row continuation ∨ hsame row provenance ∨ hsame row localName ∨
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row checkerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle checkerRead pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory checkerRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger handoffContinuationChecker checkerReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed handoffUnary continuationUnary handoffContinuationChecker
  have checkerSource :
      (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row) checkerRead := by
    exact ⟨hsame_refl checkerRead, checkerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                hsame row continuation ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row checkerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle checkerRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro checkerRead checkerSource
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, checkerReadPkg, realSealPkg⟩
  }
  exact ⟨cert, checkerUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
