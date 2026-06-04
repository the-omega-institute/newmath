import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondSourceFaceRetention [AskSetup] [PackageSetup]
    {closedSub residual candidate frontier diamond bounded socket l10 dyadicFace streamFace
      regSeqFace realFace sourceRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont closedSub residual frontier →
      Cont frontier candidate diamond →
        Cont diamond socket bounded →
          Cont bounded l10 sourceRead →
            Cont l10 dyadicFace streamFace →
              Cont streamFace regSeqFace realFace →
                PkgSig bundle provenance pkg →
                  PkgSig bundle localName pkg →
                    UnaryHistory closedSub →
                      UnaryHistory residual →
                        UnaryHistory candidate →
                          UnaryHistory socket →
                            UnaryHistory l10 →
                              UnaryHistory dyadicFace →
                                UnaryHistory regSeqFace →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row sourceRead ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row dyadicFace ∨ hsame row streamFace ∨
                                          hsame row regSeqFace ∨ hsame row realFace ∨
                                            hsame row sourceRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg)
                                      hsame ∧
                                    UnaryHistory frontier ∧ UnaryHistory diamond ∧
                                      UnaryHistory bounded ∧ UnaryHistory sourceRead ∧
                                        UnaryHistory streamFace ∧ UnaryHistory realFace := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro closedResidualFrontier frontierCandidateDiamond diamondSocketBounded
    boundedL10Source l10DyadicStream streamRegSeqReal provenancePkg localNamePkg
    closedSubUnary residualUnary candidateUnary socketUnary l10Unary dyadicFaceUnary
    regSeqFaceUnary
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed closedSubUnary residualUnary closedResidualFrontier
  have diamondUnary : UnaryHistory diamond :=
    unary_cont_closed frontierUnary candidateUnary frontierCandidateDiamond
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed diamondUnary socketUnary diamondSocketBounded
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed boundedUnary l10Unary boundedL10Source
  have streamFaceUnary : UnaryHistory streamFace :=
    unary_cont_closed l10Unary dyadicFaceUnary l10DyadicStream
  have realFaceUnary : UnaryHistory realFace :=
    unary_cont_closed streamFaceUnary regSeqFaceUnary streamRegSeqReal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicFace ∨ hsame row streamFace ∨ hsame row regSeqFace ∨
              hsame row realFace ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceReadUnary⟩
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, frontierUnary, diamondUnary, boundedUnary, sourceReadUnary, streamFaceUnary,
      realFaceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
