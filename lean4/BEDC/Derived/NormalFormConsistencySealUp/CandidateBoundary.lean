import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealCandidateBoundary
    {T F N K X H C P L typedFalse normalTheorem boundaryRead candidateRead residualRead
      endpointRead : BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              UnaryHistory C ->
                UnaryHistory L ->
                  Cont T F typedFalse ->
                    Cont N K normalTheorem ->
                      Cont normalTheorem X boundaryRead ->
                        Cont boundaryRead C candidateRead ->
                          Cont candidateRead L residualRead ->
                            Cont residualRead K endpointRead ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row T ∨ hsame row F ∨ hsame row N ∨
                                      hsame row K ∨ hsame row X ∨
                                        hsame row candidateRead ∨
                                          hsame row residualRead ∨ hsame row endpointRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont boundaryRead C candidateRead ∧
                                      Cont candidateRead L residualRead ∧
                                        Cont residualRead K endpointRead)
                                  hsame ∧
                                UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                                  UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary nUnary kUnary xUnary cUnary lUnary typedFalseRoute
    normalTheoremRoute boundaryRoute candidateRoute residualRoute endpointRoute
  have _typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed tUnary fUnary typedFalseRoute
  have normalTheoremUnary : UnaryHistory normalTheorem :=
    unary_cont_closed nUnary kUnary normalTheoremRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed normalTheoremUnary xUnary boundaryRoute
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed boundaryReadUnary cUnary candidateRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateReadUnary lUnary residualRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed residualReadUnary kUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨
              hsame row X ∨ hsame row candidateRead ∨ hsame row residualRead ∨
                hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundaryRead C candidateRead ∧
              Cont candidateRead L residualRead ∧ Cont residualRead K endpointRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointReadUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, candidateRoute, residualRoute, endpointRoute⟩
  }
  exact ⟨cert, candidateReadUnary, residualReadUnary, endpointReadUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
