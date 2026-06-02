import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealCandidateRoute
    {typing falseRow normalRow theoremRow boundary transport replay provenance localName
      candidateRead routeRead : BHist} :
    Cont typing normalRow candidateRead →
      Cont candidateRead theoremRow routeRead →
        UnaryHistory typing →
          UnaryHistory normalRow →
            UnaryHistory theoremRow →
              UnaryHistory candidateRead ∧ UnaryHistory routeRead ∧ hsame boundary boundary := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro candidateRoute theoremRoute typingUnary normalUnary theoremUnary
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed typingUnary normalUnary candidateRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed candidateUnary theoremUnary theoremRoute
  exact ⟨candidateUnary, routeUnary, hsame_refl boundary⟩

theorem NormalFormConsistencySealMetaCICCriticalPathHandoff
    {T F N K X H C P L candidateRead closedRead residualRead boundaryRead handoffRead :
      BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              UnaryHistory H ->
                UnaryHistory C ->
                  Cont T F candidateRead ->
                    Cont N K closedRead ->
                      Cont candidateRead closedRead residualRead ->
                        Cont residualRead H boundaryRead ->
                          Cont boundaryRead C handoffRead ->
                            SemanticNameCert
                                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row F ∨ hsame row N ∨
                                    hsame row K ∨ hsame row X ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row L ∨
                                        hsame row handoffRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont residualRead H boundaryRead ∧
                                    Cont boundaryRead C handoffRead)
                                hsame ∧
                              UnaryHistory candidateRead ∧
                                UnaryHistory closedRead ∧
                                  UnaryHistory residualRead ∧
                                    UnaryHistory boundaryRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary nUnary kUnary _xUnary hUnary cUnary candidateRoute closedRoute
    residualRoute boundaryRoute handoffRoute
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed tUnary fUnary candidateRoute
  have closedUnary : UnaryHistory closedRead :=
    unary_cont_closed nUnary kUnary closedRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary closedUnary residualRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed residualUnary hUnary boundaryRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed boundaryUnary cUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨
              hsame row X ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row L ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont residualRead H boundaryRead ∧
              Cont boundaryRead C handoffRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact ⟨source.right, boundaryRoute, handoffRoute⟩
  }
  exact
    ⟨cert, candidateUnary, closedUnary, residualUnary, boundaryUnary, handoffUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
