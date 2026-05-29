import BEDC.Derived.MetaCICCriticalPathUp.OpenPhaseConsumerTotality

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRealCompletionBudgetTriangle [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal completionRead sourceRead snRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal provenance completionRead →
        Cont dyadic stream sourceRead →
          Cont strongNorm normalForm snRead →
            Cont handoff obstruction socketRead →
              PkgSig bundle completionRead pkg →
                PkgSig bundle sourceRead pkg →
                  PkgSig bundle snRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                            hsame row realSeal ∨ hsame row completionRead ∨
                              hsame row sourceRead ∨ hsame row snRead ∨
                                hsame row socketRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
                            PkgSig bundle sourceRead pkg ∧ PkgSig bundle snRead pkg ∧
                              PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory completionRead ∧ UnaryHistory sourceRead ∧
                        UnaryHistory snRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger realSealProvenanceCompletion dyadicStreamSource strongNormNormalFormSnRead
    handoffObstructionSocket completionPkg sourcePkg snPkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, _continuationUnary, provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realSealUnary provenanceUnary realSealProvenanceCompletion
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have snUnary : UnaryHistory snRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalFormSnRead
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row completionRead ∨ hsame row sourceRead ∨
                hsame row snRead ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle completionRead pkg ∧
              PkgSig bundle sourceRead pkg ∧ PkgSig bundle snRead pkg ∧
                PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionPkg, sourcePkg, snPkg, realSealPkg⟩
  }
  exact ⟨cert, completionUnary, sourceUnary, snUnary, socketUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
