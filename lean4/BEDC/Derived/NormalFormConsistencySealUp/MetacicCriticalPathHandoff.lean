import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealMetacicCriticalPathHandoff
    {T F N K X _H C P L candidateRead boundaryRead scheduleRead handoffRead : BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              UnaryHistory C ->
                UnaryHistory P ->
                  UnaryHistory L ->
                    Cont T F candidateRead ->
                      Cont N K boundaryRead ->
                        Cont boundaryRead C scheduleRead ->
                          Cont scheduleRead P handoffRead ->
                            SemanticNameCert
                                (fun row : BHist =>
                                  hsame row handoffRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row T ∨ hsame row F ∨ hsame row N ∨
                                    hsame row K ∨ hsame row X ∨ hsame row candidateRead ∨
                                      hsame row boundaryRead ∨ hsame row scheduleRead ∨
                                        hsame row handoffRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont boundaryRead C scheduleRead ∧
                                    Cont scheduleRead P handoffRead)
                                hsame ∧
                              UnaryHistory candidateRead ∧ UnaryHistory boundaryRead ∧
                                UnaryHistory scheduleRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary nUnary kUnary _xUnary cUnary pUnary _lUnary candidateRoute
    boundaryRoute scheduleRoute handoffRoute
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed tUnary fUnary candidateRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed nUnary kUnary boundaryRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed boundaryUnary cUnary scheduleRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed scheduleUnary pUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row candidateRead ∨ hsame row boundaryRead ∨ hsame row scheduleRead ∨
                hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundaryRead C scheduleRead ∧
              Cont scheduleRead P handoffRead)
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scheduleRoute, handoffRoute⟩
  }
  exact ⟨cert, candidateUnary, boundaryUnary, scheduleUnary, handoffUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
