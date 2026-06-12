import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedSNBoundedDischargeRoute [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead witnessRead
      fairnessRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName candidateRead ->
        Cont candidateRead realSeal residualRead ->
          Cont residualRead obstruction witnessRead ->
            Cont witnessRead discharge fairnessRead ->
              Cont fairnessRead handoff boundedRead ->
                PkgSig bundle boundedRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row witnessRead ∨ hsame row fairnessRead ∨
                            hsame row boundedRead) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row witnessRead ∨ hsame row fairnessRead ∨
                            hsame row boundedRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundedRead pkg)
                      hsame ∧
                    UnaryHistory boundedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateSealResidual residualObstructionWitness
    witnessDischargeFairness fairnessHandoffBounded boundedPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary realSealUnary candidateSealResidual
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionWitness
  have fairnessUnary : UnaryHistory fairnessRead :=
    unary_cont_closed witnessUnary dischargeUnary witnessDischargeFairness
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed fairnessUnary handoffUnary fairnessHandoffBounded
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row residualRead ∨ hsame row witnessRead ∨
              hsame row fairnessRead ∨ hsame row boundedRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row witnessRead ∨
              hsame row fairnessRead ∨ hsame row boundedRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle boundedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundedRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl boundedRead)))), boundedUnary⟩
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
          | inl sameCandidate =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
          | inr tail =>
              cases tail with
              | inl sameResidual =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameResidual))
              | inr tail =>
                  cases tail with
                  | inl sameWitness =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameWitness)))
                  | inr tail =>
                      cases tail with
                      | inl sameFairness =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl
                                    (hsame_trans (hsame_symm sameRows) sameFairness))))
                      | inr sameBounded =>
                          exact
                            Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (hsame_trans (hsame_symm sameRows) sameBounded))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundedPkg⟩
  }
  exact ⟨cert, boundedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
