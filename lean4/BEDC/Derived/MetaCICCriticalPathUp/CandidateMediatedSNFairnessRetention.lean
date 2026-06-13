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

theorem MetaCICCriticalPathCandidateMediatedSNFairnessRetention
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead fairnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName candidateRead ->
        Cont candidateRead handoff fairnessRead ->
          PkgSig bundle fairnessRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row candidateRead ∨ hsame row fairnessRead ∨ hsame row stream ∨
                    hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row candidateRead ∨ hsame row fairnessRead ∨ hsame row stream ∨
                    hsame row regseq ∨ hsame row realSeal)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle fairnessRead pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory candidateRead ∧ UnaryHistory fairnessRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateHandoffFairness fairnessPkg
  obtain ⟨packet, _dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have fairnessUnary : UnaryHistory fairnessRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFairness
  have sourceCandidate :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row fairnessRead ∨ hsame row stream ∨
          hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row) candidateRead := by
    exact ⟨Or.inl (hsame_refl candidateRead), candidateUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row fairnessRead ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row fairnessRead ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle fairnessRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro candidateRead sourceCandidate
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
          ⟨by
            cases source.left with
            | inl sameCandidate =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
            | inr rest =>
                cases rest with
                | inl sameFairness =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFairness))
                | inr rest =>
                    cases rest with
                    | inl sameStream =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameStream)))
                    | inr rest =>
                        cases rest with
                        | inl sameRegseq =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameRegseq))))
                        | inr sameRealSeal =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (hsame_trans (hsame_symm sameRows) sameRealSeal)))),
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, fairnessPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, fairnessUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
