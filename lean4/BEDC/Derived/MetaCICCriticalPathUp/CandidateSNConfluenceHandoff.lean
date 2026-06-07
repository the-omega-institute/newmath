import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.Derived.MetaCICCriticalPathUp.ResidualDiamondLocalConfluenceFrontier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateSNConfluenceHandoff [AskSetup] [PackageSetup]
    {closedSub residual candidate frontier diamond bounded socket l10 dyadicFace streamFace
      regSeqFace realFace sourceRead localRead snRead confluenceRead : BHist}
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
                                Cont candidate realFace snRead →
                                  Cont snRead diamond confluenceRead →
                                    PkgSig bundle confluenceRead pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row confluenceRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row candidate ∨ hsame row frontier ∨
                                              hsame row diamond ∨ hsame row bounded ∨
                                                hsame row socket ∨ hsame row dyadicFace ∨
                                                  hsame row streamFace ∨
                                                    hsame row regSeqFace ∨
                                                      hsame row realFace ∨
                                                        hsame row confluenceRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont candidate realFace snRead ∧
                                              Cont snRead diamond confluenceRead ∧
                                                PkgSig bundle confluenceRead pkg)
                                          hsame ∧ UnaryHistory snRead ∧
                                        UnaryHistory confluenceRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro closedResidualFrontier frontierCandidateDiamond diamondSocketBounded
    boundedL10Source l10DyadicStream streamRegSeqReal localPkg closedUnary
    residualUnary candidateUnary socketUnary l10Unary dyadicUnary regSeqUnary
    candidateRealSN snDiamondConfluence confluencePkg
  have residualFrontier :
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
          hsame ∧
        UnaryHistory frontier ∧ UnaryHistory diamond ∧ UnaryHistory bounded ∧
          UnaryHistory streamFace ∧ UnaryHistory realFace ∧ UnaryHistory sourceRead :=
    MetaCICCriticalPathResidualDiamondLocalConfluenceFrontier
      closedResidualFrontier frontierCandidateDiamond diamondSocketBounded boundedL10Source
      l10DyadicStream streamRegSeqReal localPkg closedUnary residualUnary candidateUnary
      socketUnary l10Unary dyadicUnary regSeqUnary
  obtain ⟨_frontierCert, frontierUnary, diamondUnary, boundedUnary, streamFaceUnary,
    realFaceUnary, _sourceUnary⟩ := residualFrontier
  have snUnary : UnaryHistory snRead :=
    unary_cont_closed candidateUnary realFaceUnary candidateRealSN
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed snUnary diamondUnary snDiamondConfluence
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidate ∨ hsame row frontier ∨ hsame row diamond ∨
              hsame row bounded ∨ hsame row socket ∨ hsame row dyadicFace ∨
                hsame row streamFace ∨ hsame row regSeqFace ∨ hsame row realFace ∨
                  hsame row confluenceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont candidate realFace snRead ∧
              Cont snRead diamond confluenceRead ∧ PkgSig bundle confluenceRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro confluenceRead ⟨hsame_refl confluenceRead, confluenceUnary⟩
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
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, candidateRealSN, snDiamondConfluence, confluencePkg⟩
  }
  exact ⟨cert, snUnary, confluenceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
