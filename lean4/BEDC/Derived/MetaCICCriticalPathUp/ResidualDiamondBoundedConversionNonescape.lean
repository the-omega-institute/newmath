import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondBoundedConversionNonescape [AskSetup] [PackageSetup]
    {closedSub residual candidate frontier diamond bounded typedBoundary dyadicFace streamFace
      regSeqFace realFace sourceRead provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont closedSub residual frontier ->
      Cont frontier candidate diamond ->
        Cont diamond typedBoundary bounded ->
          Cont bounded dyadicFace streamFace ->
            Cont streamFace regSeqFace realFace ->
              Cont realFace localName sourceRead ->
                PkgSig bundle provenance pkg ->
                  PkgSig bundle localName pkg ->
                    UnaryHistory closedSub ->
                      UnaryHistory residual ->
                        UnaryHistory candidate ->
                          UnaryHistory typedBoundary ->
                            UnaryHistory dyadicFace ->
                              UnaryHistory regSeqFace ->
                                UnaryHistory localName ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row sourceRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row sourceRead ∨ hsame row closedSub ∨
                                          hsame row residual ∨ hsame row candidate ∨
                                            hsame row frontier ∨ hsame row diamond ∨
                                              hsame row bounded ∨ hsame row typedBoundary ∨
                                                hsame row dyadicFace ∨
                                                  hsame row streamFace ∨
                                                    hsame row regSeqFace ∨
                                                      hsame row realFace ∨
                                                        hsame row localName)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont closedSub residual frontier ∧
                                            Cont frontier candidate diamond ∧
                                              Cont diamond typedBoundary bounded ∧
                                                Cont bounded dyadicFace streamFace ∧
                                                  Cont streamFace regSeqFace realFace ∧
                                                    Cont realFace localName sourceRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle localName pkg)
                                      hsame ∧
                                    UnaryHistory frontier ∧ UnaryHistory diamond ∧
                                      UnaryHistory bounded ∧ UnaryHistory streamFace ∧
                                        UnaryHistory realFace ∧ UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro closedResidual residualCandidate diamondTyped boundedDyadic streamReal
    realLocalSource provenancePkg localNamePkg closedUnary residualUnary candidateUnary
    typedBoundaryUnary dyadicUnary regSeqUnary localNameUnary
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed closedUnary residualUnary closedResidual
  have diamondUnary : UnaryHistory diamond :=
    unary_cont_closed frontierUnary candidateUnary residualCandidate
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed diamondUnary typedBoundaryUnary diamondTyped
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed boundedUnary dyadicUnary boundedDyadic
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed streamUnary regSeqUnary streamReal
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed realUnary localNameUnary realLocalSource
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row closedSub ∨ hsame row residual ∨
              hsame row candidate ∨ hsame row frontier ∨ hsame row diamond ∨
                hsame row bounded ∨ hsame row typedBoundary ∨ hsame row dyadicFace ∨
                  hsame row streamFace ∨ hsame row regSeqFace ∨ hsame row realFace ∨
                    hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont closedSub residual frontier ∧
              Cont frontier candidate diamond ∧ Cont diamond typedBoundary bounded ∧
                Cont bounded dyadicFace streamFace ∧ Cont streamFace regSeqFace realFace ∧
                  Cont realFace localName sourceRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, closedResidual, residualCandidate, diamondTyped, boundedDyadic,
          streamReal, realLocalSource, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, frontierUnary, diamondUnary, boundedUnary, streamUnary, realUnary,
      sourceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
