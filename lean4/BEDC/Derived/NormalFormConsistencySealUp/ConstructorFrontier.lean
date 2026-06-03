import BEDC.Derived.NormalFormConsistencySealUp

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealConstructorFrontier
    {T F N K X H C P L typedFalse normalTheorem closedRoute boundaryRead replayRead
      namedRead : BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory N ->
          UnaryHistory K ->
            UnaryHistory X ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory L ->
                      Cont T F typedFalse ->
                        Cont N K normalTheorem ->
                          Cont typedFalse normalTheorem closedRoute ->
                            Cont normalTheorem X boundaryRead ->
                              Cont boundaryRead C replayRead ->
                                Cont replayRead H namedRead ->
                                  hsame namedRead closedRoute ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row T ∨ hsame row F ∨ hsame row N ∨
                                            hsame row K ∨ hsame row X ∨
                                              hsame row closedRoute ∨ hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ hsame row namedRead)
                                        hsame ∧
                                      UnaryHistory typedFalse ∧
                                        UnaryHistory normalTheorem ∧
                                          UnaryHistory closedRoute ∧
                                            UnaryHistory boundaryRead ∧
                                              UnaryHistory replayRead ∧
                                                UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary nUnary kUnary xUnary hUnary cUnary _pUnary _lUnary typedFalseRoute
    normalTheoremRoute closedRouteRoute boundaryRoute replayRoute namedRoute sameNamedClosed
  have typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed tUnary fUnary typedFalseRoute
  have normalTheoremUnary : UnaryHistory normalTheorem :=
    unary_cont_closed nUnary kUnary normalTheoremRoute
  have closedRouteUnary : UnaryHistory closedRoute :=
    unary_cont_closed typedFalseUnary normalTheoremUnary closedRouteRoute
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed normalTheoremUnary xUnary boundaryRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundaryReadUnary cUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary hUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row N ∨ hsame row K ∨ hsame row X ∨
              hsame row closedRoute ∨ hsame row namedRead)
          (fun row : BHist => UnaryHistory row ∧ hsame row namedRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro namedRead ⟨hsame_refl namedRead, namedReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, source.left⟩
  }
  exact
    ⟨cert, typedFalseUnary, normalTheoremUnary, closedRouteUnary, boundaryReadUnary,
      replayReadUnary, namedReadUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
