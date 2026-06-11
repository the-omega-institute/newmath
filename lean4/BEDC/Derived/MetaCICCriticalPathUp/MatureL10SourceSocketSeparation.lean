import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathMatureL10SourceSocketSeparation [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead socketRead
      maturityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff frontierRead →
          Cont frontierRead obstruction socketRead →
            Cont socketRead realSeal maturityRead →
              PkgSig bundle socketRead pkg →
                PkgSig bundle maturityRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row socketRead ∨ hsame row maturityRead ∨
                          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                            hsame row realSeal) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row frontierRead ∨ hsame row socketRead ∨
                          hsame row maturityRead ∨ hsame row dyadic ∨
                            hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                          PkgSig bundle maturityRead pkg ∧ PkgSig bundle realSeal pkg)
                      hsame ∧
                    UnaryHistory socketRead ∧ UnaryHistory maturityRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateHandoffFrontier
    frontierObstructionSocket socketRealSealMaturity socketPkg maturityPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have maturityUnary : UnaryHistory maturityRead :=
    unary_cont_closed socketUnary realSealUnary socketRealSealMaturity
  have socketSource :
      (fun row : BHist =>
        (hsame row socketRead ∨ hsame row maturityRead ∨ hsame row dyadic ∨
          hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
          UnaryHistory row) socketRead := by
    exact ⟨Or.inl (hsame_refl socketRead), socketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row socketRead ∨ hsame row maturityRead ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row frontierRead ∨ hsame row socketRead ∨ hsame row maturityRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              PkgSig bundle maturityRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead socketSource
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSocket =>
          exact Or.inr (Or.inl sameSocket)
      | inr rest =>
          cases rest with
          | inl sameMaturity =>
              exact Or.inr (Or.inr (Or.inl sameMaturity))
          | inr rest =>
              cases rest with
              | inl sameDyadic =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl sameDyadic)))
              | inr rest =>
                  cases rest with
                  | inl sameStream =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream))))
                  | inr rest =>
                      cases rest with
                      | inl sameRegseq =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl sameRegseq)))))
                      | inr sameRealSeal =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inr sameRealSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketPkg, maturityPkg, realSealPkg⟩
  }
  exact ⟨cert, socketUnary, maturityUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
