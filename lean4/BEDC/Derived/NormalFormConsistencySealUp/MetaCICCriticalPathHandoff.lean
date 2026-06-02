import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealMetaCICCriticalPathHandoff
    {T F N K X H C P L candidateRead residualRead joinRead scheduleRead sourcedRead
      frontierRead : BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory L ->
                      Cont T F candidateRead ->
                        Cont candidateRead N residualRead ->
                          Cont residualRead K joinRead ->
                            Cont joinRead C scheduleRead ->
                              Cont scheduleRead P sourcedRead ->
                                Cont X L frontierRead ->
                                  UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                                    UnaryHistory joinRead ∧ UnaryHistory scheduleRead ∧
                                      UnaryHistory sourcedRead ∧ UnaryHistory frontierRead ∧
                                        SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row frontierRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row T ∨ hsame row F ∨ hsame row N ∨
                                              hsame row K ∨ hsame row X ∨ hsame row H ∨
                                                hsame row C ∨ hsame row P ∨ hsame row L ∨
                                                  hsame row candidateRead ∨
                                                    hsame row residualRead ∨
                                                      hsame row frontierRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont X L frontierRead)
                                          hsame ∧
                                          hsame frontierRead (append X L) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary nUnary kUnary xUnary _hUnary cUnary pUnary lUnary candidateRoute
    residualRoute joinRoute scheduleRoute sourcedRoute frontierRoute
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed tUnary fUnary candidateRoute
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary nUnary residualRoute
  have joinUnary : UnaryHistory joinRead :=
    unary_cont_closed residualUnary kUnary joinRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed joinUnary cUnary scheduleRoute
  have sourcedUnary : UnaryHistory sourcedRead :=
    unary_cont_closed scheduleUnary pUnary sourcedRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed xUnary lUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row L ∨
                hsame row candidateRead ∨ hsame row residualRead ∨ hsame row frontierRead)
          (fun row : BHist => UnaryHistory row ∧ Cont X L frontierRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierRoute⟩
  }
  have frontierSame : hsame frontierRead (append X L) := by
    cases frontierRoute
    rfl
  exact
    ⟨candidateUnary, residualUnary, joinUnary, scheduleUnary, sourcedUnary, frontierUnary,
      cert, frontierSame⟩

end BEDC.Derived.NormalFormConsistencySealUp
