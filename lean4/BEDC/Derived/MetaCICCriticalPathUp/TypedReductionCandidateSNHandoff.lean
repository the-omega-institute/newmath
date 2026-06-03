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

theorem MetaCICCriticalPathTypedReductionCandidateSNHandoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal typedRead checkerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont strongNorm normalForm typedRead →
        Cont typedRead discharge checkerRead →
          PkgSig bundle checkerRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row typedRead ∨ hsame row checkerRead ∨ hsame row discharge ∨
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row discharge ∨
                    hsame row handoff ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row regseq ∨ hsame row realSeal ∨ hsame row typedRead ∨
                        hsame row checkerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont strongNorm normalForm typedRead ∧
                    Cont typedRead discharge checkerRead ∧ PkgSig bundle checkerRead pkg ∧
                      PkgSig bundle realSeal pkg)
                hsame ∧ UnaryHistory typedRead ∧ UnaryHistory checkerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger typedRoute checkerRoute checkerPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have typedUnary : UnaryHistory typedRead :=
    unary_cont_closed strongNormUnary normalFormUnary typedRoute
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed typedUnary dischargeUnary checkerRoute
  have sourceChecker :
      (fun row : BHist =>
        (hsame row typedRead ∨ hsame row checkerRead ∨ hsame row discharge ∨
          hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
          UnaryHistory row) checkerRead := by
    exact ⟨Or.inr (Or.inl (hsame_refl checkerRead)), checkerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row typedRead ∨ hsame row checkerRead ∨ hsame row discharge ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row discharge ∨
              hsame row handoff ∨ hsame row dyadic ∨ hsame row stream ∨
                hsame row regseq ∨ hsame row realSeal ∨ hsame row typedRead ∨
                  hsame row checkerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont strongNorm normalForm typedRead ∧
              Cont typedRead discharge checkerRead ∧ PkgSig bundle checkerRead pkg ∧
                PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro checkerRead sourceChecker
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
            | inl rowTyped =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) rowTyped)
            | inr rest =>
                cases rest with
                | inl rowChecker =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowChecker))
                | inr rest =>
                    cases rest with
                    | inl rowDischarge =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) rowDischarge)))
                    | inr rest =>
                        cases rest with
                        | inl rowDyadic =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) rowDyadic))))
                        | inr rest =>
                            cases rest with
                            | inl rowStream =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl
                                            (hsame_trans (hsame_symm sameRows) rowStream)))))
                            | inr rest =>
                                cases rest with
                                | inl rowRegseq =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inl
                                                  (hsame_trans
                                                    (hsame_symm sameRows) rowRegseq))))))
                                | inr rowRealSeal =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (hsame_trans
                                                    (hsame_symm sameRows) rowRealSeal))))))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl rowTyped =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl rowTyped))))))))
      | inr rest =>
          cases rest with
          | inl rowChecker =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr rowChecker))))))))
          | inr rest =>
              cases rest with
              | inl rowDischarge =>
                  exact Or.inr (Or.inr (Or.inl rowDischarge))
              | inr rest =>
                  cases rest with
                  | inl rowDyadic =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowDyadic))))
                  | inr rest =>
                      cases rest with
                      | inl rowStream =>
                          exact
                            Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rowStream)))))
                      | inr rest =>
                          cases rest with
                          | inl rowRegseq =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr (Or.inr (Or.inl rowRegseq))))))
                          | inr rowRealSeal =>
                              exact
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inr (Or.inl rowRealSeal)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, typedRoute, checkerRoute, checkerPkg, realSealPkg⟩
  }
  exact ⟨cert, typedUnary, checkerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
