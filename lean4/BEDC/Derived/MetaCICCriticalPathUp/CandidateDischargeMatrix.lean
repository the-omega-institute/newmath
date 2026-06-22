import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateDischargeMatrix [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead checkerRead
      dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal residualRead →
          Cont residualRead obstruction checkerRead →
            Cont checkerRead discharge dischargeRead →
              PkgSig bundle dischargeRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row checkerRead ∨ hsame row dischargeRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row candidateRead ∨
                          hsame row residualRead ∨ hsame row checkerRead ∨
                            hsame row dischargeRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧
                        PkgSig bundle dischargeRead pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory checkerRead ∧ UnaryHistory dischargeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateRealResidual
    residualObstructionChecker checkerDischargeRead dischargePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary realSealUnary candidateRealResidual
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionChecker
  have dischargeUnaryRead : UnaryHistory dischargeRead :=
    unary_cont_closed checkerUnary dischargeUnary checkerDischargeRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row residualRead ∨ hsame row checkerRead ∨
                hsame row dischargeRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
              hsame row candidateRead ∨ hsame row residualRead ∨ hsame row checkerRead ∨
                hsame row dischargeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧ PkgSig bundle dischargeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dischargeRead
          ⟨Or.inr (Or.inr (Or.inr (hsame_refl dischargeRead))), dischargeUnaryRead⟩
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
        have transportedUnary : UnaryHistory _ := unary_transport source.right sameRows
        cases source.left with
        | inl sameCandidate =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate),
                transportedUnary⟩
        | inr rest =>
            cases rest with
            | inl sameResidual =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameResidual)),
                    transportedUnary⟩
            | inr rest =>
                cases rest with
                | inl sameChecker =>
                    exact
                      ⟨Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameChecker))),
                        transportedUnary⟩
                | inr sameDischarge =>
                    exact
                      ⟨Or.inr (Or.inr
                        (Or.inr (hsame_trans (hsame_symm sameRows) sameDischarge))),
                        transportedUnary⟩
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
              | inl sameChecker =>
                  exact
                    Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl sameChecker))))))
              | inr sameDischarge =>
                  exact
                    Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr sameDischarge))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealPkg, dischargePkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, checkerUnary, dischargeUnaryRead⟩

end BEDC.Derived.MetaCICCriticalPathUp
