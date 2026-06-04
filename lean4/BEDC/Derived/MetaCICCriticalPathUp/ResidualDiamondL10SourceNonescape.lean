import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondL10SourceNonescape [AskSetup] [PackageSetup]
    {closedSub residual candidate frontier diamond bounded socket l10 dyadicFace streamFace
      regSeqFace realFace sourceRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont closedSub residual frontier ->
      Cont frontier candidate diamond ->
        Cont diamond socket bounded ->
          Cont bounded l10 sourceRead ->
            Cont l10 dyadicFace streamFace ->
              Cont streamFace regSeqFace realFace ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle localName pkg ->
                    UnaryHistory closedSub ->
                      UnaryHistory residual ->
                        UnaryHistory candidate ->
                          UnaryHistory socket ->
                            UnaryHistory l10 ->
                              UnaryHistory dyadicFace ->
                                UnaryHistory regSeqFace ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row sourceRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row closedSub ∨ hsame row residual ∨
                                          hsame row candidate ∨ hsame row frontier ∨
                                            hsame row diamond ∨ hsame row bounded ∨
                                              hsame row socket ∨ hsame row l10 ∨
                                                hsame row dyadicFace ∨
                                                  hsame row streamFace ∨
                                                    hsame row regSeqFace ∨
                                                      hsame row realFace ∨
                                                        hsame row sourceRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont closedSub residual frontier ∧
                                            Cont frontier candidate diamond ∧
                                              Cont diamond socket bounded ∧
                                                Cont bounded l10 sourceRead ∧
                                                  Cont l10 dyadicFace streamFace ∧
                                                    Cont streamFace regSeqFace realFace ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle localName pkg)
                                      hsame ∧
                                    UnaryHistory frontier ∧ UnaryHistory diamond ∧
                                      UnaryHistory bounded ∧ UnaryHistory sourceRead ∧
                                        UnaryHistory streamFace ∧ UnaryHistory realFace := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro closedResidual residualCandidate diamondSocket boundedSource l10Stream
    streamReal provenancePkg localNamePkg closedUnary residualUnary candidateUnary socketUnary
    l10Unary dyadicUnary regSeqUnary
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed closedUnary residualUnary closedResidual
  have diamondUnary : UnaryHistory diamond :=
    unary_cont_closed frontierUnary candidateUnary residualCandidate
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed diamondUnary socketUnary diamondSocket
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed boundedUnary l10Unary boundedSource
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed l10Unary dyadicUnary l10Stream
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed streamUnary regSeqUnary streamReal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closedSub ∨ hsame row residual ∨ hsame row candidate ∨
              hsame row frontier ∨ hsame row diamond ∨ hsame row bounded ∨
                hsame row socket ∨ hsame row l10 ∨ hsame row dyadicFace ∨
                  hsame row streamFace ∨ hsame row regSeqFace ∨ hsame row realFace ∨
                    hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont closedSub residual frontier ∧
              Cont frontier candidate diamond ∧ Cont diamond socket bounded ∧
                Cont bounded l10 sourceRead ∧ Cont l10 dyadicFace streamFace ∧
                  Cont streamFace regSeqFace realFace ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
          (Or.inr (Or.inr (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, closedResidual, residualCandidate, diamondSocket, boundedSource,
          l10Stream, streamReal, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, frontierUnary, diamondUnary, boundedUnary, sourceUnary, streamUnary,
      realUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
