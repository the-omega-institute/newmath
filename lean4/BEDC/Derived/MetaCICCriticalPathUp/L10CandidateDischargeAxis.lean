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

theorem MetaCICCriticalPathL10CandidateDischargeAxis [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead typedExampleRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName candidateRead ->
        Cont candidateRead realSeal residualRead ->
          Cont residualRead discharge typedExampleRead ->
            Cont typedExampleRead obstruction publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row candidateRead ∨ hsame row residualRead ∨
                        hsame row typedExampleRead ∨ hsame row publicRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row candidateRead ∨
                          hsame row residualRead ∨ hsame row typedExampleRead ∨
                            hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧
                        PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory typedExampleRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateRealSealResidual
    residualDischargeTyped typedObstructionPublic publicPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary realSealUnary candidateRealSealResidual
  have typedUnary : UnaryHistory typedExampleRead :=
    unary_cont_closed residualUnary dischargeUnary residualDischargeTyped
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed typedUnary obstructionUnary typedObstructionPublic
  have publicSource :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row residualRead ∨
          hsame row typedExampleRead ∨ hsame row publicRead) ∧ UnaryHistory row)
          publicRead := by
    exact ⟨Or.inr (Or.inr (Or.inr (hsame_refl publicRead))), publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row residualRead ∨
              hsame row typedExampleRead ∨ hsame row publicRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row candidateRead ∨ hsame row residualRead ∨
                hsame row typedExampleRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead publicSource
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
        have otherUnary : UnaryHistory _other := unary_transport source.right sameRows
        cases source.left with
        | inl sameCandidate =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate), otherUnary⟩
        | inr rest =>
            cases rest with
            | inl sameResidual =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameResidual)),
                    otherUnary⟩
            | inr rest =>
                cases rest with
                | inl sameTyped =>
                    exact
                      ⟨Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTyped))),
                        otherUnary⟩
                | inr samePublic =>
                    exact
                      ⟨Or.inr
                        (Or.inr
                          (Or.inr (hsame_trans (hsame_symm sameRows) samePublic))),
                        otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCandidate =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameCandidate))))
      | inr rest =>
          cases rest with
          | inl sameResidual =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameResidual)))))
          | inr rest =>
              cases rest with
              | inl sameTyped =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inl sameTyped))))))
              | inr samePublic =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inr samePublic))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealPkg, publicPkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, typedUnary, publicUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
