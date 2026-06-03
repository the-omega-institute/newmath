import BEDC.Derived.NormalFormConsistencySealUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NormalFormConsistencySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem NormalFormConsistencySealResidualContextObligation
    {T F N K X H C P L typedFalse residualRead replayRead namedRead : BHist} :
    UnaryHistory T ->
      UnaryHistory F ->
        UnaryHistory X ->
          UnaryHistory H ->
            UnaryHistory C ->
              UnaryHistory L ->
                Cont T F typedFalse ->
                  Cont typedFalse X residualRead ->
                    Cont residualRead C replayRead ->
                      Cont replayRead L namedRead ->
                        SemanticNameCert
                            (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row T ∨ hsame row F ∨ hsame row X ∨ hsame row H ∨
                                hsame row C ∨ hsame row L ∨ hsame row residualRead ∨
                                  hsame row namedRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont typedFalse X residualRead)
                            hsame ∧
                          UnaryHistory typedFalse ∧ UnaryHistory residualRead ∧
                            UnaryHistory replayRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro tUnary fUnary xUnary _hUnary cUnary lUnary typedFalseRoute residualRoute
    replayRoute nameRoute
  have typedFalseUnary : UnaryHistory typedFalse :=
    unary_cont_closed tUnary fUnary typedFalseRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed typedFalseUnary xUnary residualRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed residualReadUnary cUnary replayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed replayReadUnary lUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row F ∨ hsame row X ∨ hsame row H ∨ hsame row C ∨
              hsame row L ∨ hsame row residualRead ∨ hsame row namedRead)
          (fun row : BHist => UnaryHistory row ∧ Cont typedFalse X residualRead)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, residualRoute⟩
  }
  exact
    ⟨cert, typedFalseUnary, residualReadUnary, replayReadUnary, namedReadUnary⟩

end BEDC.Derived.NormalFormConsistencySealUp
