import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathResidualDiamondBudgetSourceNonescape [AskSetup] [PackageSetup]
    {closedSub residual candidate frontier diamond bounded socket l10 sourceRead socketBudget
      candidateRoute provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont closedSub residual frontier ->
      Cont frontier candidate candidateRoute ->
        Cont candidateRoute diamond socketBudget ->
          Cont socketBudget socket bounded ->
            Cont bounded l10 sourceRead ->
              PkgSig bundle provenance pkg ->
                PkgSig bundle localName pkg ->
                  UnaryHistory closedSub ->
                    UnaryHistory residual ->
                      UnaryHistory candidate ->
                        UnaryHistory diamond ->
                          UnaryHistory socket ->
                            UnaryHistory l10 ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row sourceRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row closedSub ∨ hsame row residual ∨
                                      hsame row candidate ∨ hsame row candidateRoute ∨
                                        hsame row diamond ∨ hsame row socketBudget ∨
                                          hsame row socket ∨ hsame row bounded ∨
                                            hsame row l10 ∨ hsame row sourceRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧
                                      Cont closedSub residual frontier ∧
                                        Cont frontier candidate candidateRoute ∧
                                          Cont candidateRoute diamond socketBudget ∧
                                            Cont socketBudget socket bounded ∧
                                              Cont bounded l10 sourceRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory candidateRoute ∧ UnaryHistory socketBudget ∧
                                  UnaryHistory bounded ∧ UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro closedResidualFrontier frontierCandidateRoute candidateDiamondSocketBudget
    socketBudgetSocketBounded boundedL10Source provenancePkg localNamePkg closedUnary
    residualUnary candidateUnary diamondUnary socketUnary l10Unary
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed closedUnary residualUnary closedResidualFrontier
  have candidateRouteUnary : UnaryHistory candidateRoute :=
    unary_cont_closed frontierUnary candidateUnary frontierCandidateRoute
  have socketBudgetUnary : UnaryHistory socketBudget :=
    unary_cont_closed candidateRouteUnary diamondUnary candidateDiamondSocketBudget
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed socketBudgetUnary socketUnary socketBudgetSocketBounded
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed boundedUnary l10Unary boundedL10Source
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closedSub ∨ hsame row residual ∨ hsame row candidate ∨
              hsame row candidateRoute ∨ hsame row diamond ∨ hsame row socketBudget ∨
                hsame row socket ∨ hsame row bounded ∨ hsame row l10 ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont closedSub residual frontier ∧
              Cont frontier candidate candidateRoute ∧
                Cont candidateRoute diamond socketBudget ∧
                  Cont socketBudget socket bounded ∧ Cont bounded l10 sourceRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, closedResidualFrontier, frontierCandidateRoute,
          candidateDiamondSocketBudget, socketBudgetSocketBounded, boundedL10Source,
          provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, candidateRouteUnary, socketBudgetUnary, boundedUnary, sourceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
