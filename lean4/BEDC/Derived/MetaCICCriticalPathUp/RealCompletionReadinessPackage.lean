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

theorem MetaCICCriticalPathRealCompletionReadinessPackage [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal provenance completionRead →
        PkgSig bundle completionRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row completionRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
              UnaryHistory completionRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro ledger realSealProvenanceRead completionReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceRead
  have sourceCompletionRead :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
        completionRead := by
    exact ⟨hsame_refl completionRead, completionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletionRead
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
      exact ⟨source.right, completionReadPkg, realSealPkg⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, regseqUnary, completionReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
