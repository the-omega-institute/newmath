import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondLocalConfluenceFrontier
    [AskSetup] [PackageSetup]
    {closedSub residual candidate frontier diamond bounded socket l10 dyadicFace streamFace
      regSeqFace realFace sourceRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont closedSub residual frontier →
      Cont frontier candidate diamond →
        Cont diamond socket bounded →
          Cont bounded l10 sourceRead →
            Cont l10 dyadicFace streamFace →
              Cont streamFace regSeqFace realFace →
                PkgSig bundle localRead pkg →
                  UnaryHistory closedSub →
                    UnaryHistory residual →
                      UnaryHistory candidate →
                        UnaryHistory socket →
                          UnaryHistory l10 →
                            UnaryHistory dyadicFace →
                              UnaryHistory regSeqFace →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row sourceRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row frontier ∨ hsame row diamond ∨
                                        hsame row bounded ∨ hsame row socket ∨
                                          hsame row dyadicFace ∨ hsame row streamFace ∨
                                            hsame row regSeqFace ∨ hsame row realFace ∨
                                              hsame row sourceRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont bounded l10 sourceRead ∧
                                        Cont l10 dyadicFace streamFace ∧
                                          Cont streamFace regSeqFace realFace ∧
                                            PkgSig bundle localRead pkg)
                                    hsame ∧
                                  UnaryHistory frontier ∧ UnaryHistory diamond ∧
                                    UnaryHistory bounded ∧ UnaryHistory streamFace ∧
                                      UnaryHistory realFace ∧ UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro closedResidualFrontier frontierCandidateDiamond diamondSocketBounded
    boundedL10Source l10DyadicStream streamRegSeqReal localPkg closedUnary
    residualUnary candidateUnary socketUnary l10Unary dyadicUnary regSeqUnary
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed closedUnary residualUnary closedResidualFrontier
  have diamondUnary : UnaryHistory diamond :=
    unary_cont_closed frontierUnary candidateUnary frontierCandidateDiamond
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed diamondUnary socketUnary diamondSocketBounded
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed boundedUnary l10Unary boundedL10Source
  have streamFaceUnary : UnaryHistory streamFace :=
    unary_cont_closed l10Unary dyadicUnary l10DyadicStream
  have realFaceUnary : UnaryHistory realFace :=
    unary_cont_closed streamFaceUnary regSeqUnary streamRegSeqReal
  have sourceAtRead :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row diamond ∨ hsame row bounded ∨
              hsame row socket ∨ hsame row dyadicFace ∨ hsame row streamFace ∨
                hsame row regSeqFace ∨ hsame row realFace ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bounded l10 sourceRead ∧
              Cont l10 dyadicFace streamFace ∧ Cont streamFace regSeqFace realFace ∧
                PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceAtRead
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundedL10Source, l10DyadicStream, streamRegSeqReal, localPkg⟩
  }
  exact
    ⟨cert, frontierUnary, diamondUnary, boundedUnary, streamFaceUnary, realFaceUnary,
      sourceReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
