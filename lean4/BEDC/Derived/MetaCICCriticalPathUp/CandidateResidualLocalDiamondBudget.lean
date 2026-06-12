import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateResidualLocalDiamondBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead socketRead
      boundedRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont continuation localName candidateRead ->
        Cont candidateRead handoff residualRead ->
          Cont residualRead obstruction socketRead ->
            Cont socketRead discharge boundedRead ->
              PkgSig bundle localRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row socketRead ∨ hsame row boundedRead ∨
                            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                              hsame row realSeal) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row residualRead ∨
                        hsame row socketRead ∨ hsame row boundedRead ∨ hsame row dyadic ∨
                          hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle localRead pkg ∧
                        PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory socketRead ∧ UnaryHistory boundedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert UnaryHistory
  intro ledger candidateRoute residualRoute socketRoute boundedRoute localPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _unblockObstructionDischarge, _handoffContinuationLocal,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary candidateRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary handoffUnary residualRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed residualUnary obstructionUnary socketRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed socketUnary dischargeUnary boundedRoute
  have sourceAtBounded :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
            hsame row boundedRead ∨ hsame row dyadic ∨ hsame row stream ∨
              hsame row regseq ∨ hsame row realSeal) ∧
          UnaryHistory row) boundedRead := by
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl boundedRead)))), boundedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
                hsame row boundedRead ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row socketRead ∨
              hsame row boundedRead ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedRead sourceAtBounded
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
        intro _row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        cases source.left with
        | inl candidateSame =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) candidateSame), otherUnary⟩
        | inr rest =>
            cases rest with
            | inl residualSame =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) residualSame)),
                    otherUnary⟩
            | inr rest =>
                cases rest with
                | inl socketSame =>
                    exact
                      ⟨Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) socketSame))),
                        otherUnary⟩
                | inr rest =>
                    cases rest with
                    | inl boundedSame =>
                        exact
                          ⟨Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl (hsame_trans (hsame_symm sameRows) boundedSame)))),
                            otherUnary⟩
                    | inr rest =>
                        cases rest with
                        | inl dyadicSame =>
                            exact
                              ⟨Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inl
                                          (hsame_trans (hsame_symm sameRows) dyadicSame))))),
                                otherUnary⟩
                        | inr rest =>
                            cases rest with
                            | inl streamSame =>
                                exact
                                  ⟨Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inl
                                                (hsame_trans (hsame_symm sameRows)
                                                  streamSame)))))),
                                    otherUnary⟩
                            | inr rest =>
                                cases rest with
                                | inl regseqSame =>
                                    exact
                                      ⟨Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inl
                                                      (hsame_trans (hsame_symm sameRows)
                                                        regseqSame))))))),
                                        otherUnary⟩
                                | inr realSealSame =>
                                    exact
                                      ⟨Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (hsame_trans (hsame_symm sameRows)
                                                        realSealSame))))))),
                                        otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, socketUnary, boundedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
