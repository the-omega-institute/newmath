import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

theorem MetaCICNormalizationBudgetCarrier_nonescape
    {T C E S A _P R _H Q _L _N positiveRead refusalRead : BHist} :
    UnaryHistory T ->
      UnaryHistory C ->
        UnaryHistory E ->
          UnaryHistory S ->
            UnaryHistory A ->
              UnaryHistory R ->
                UnaryHistory Q ->
                  Cont T C E ->
                    Cont E S positiveRead ->
                      Cont R Q refusalRead ->
                        SemanticNameCert
                            (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row T ∨ hsame row C ∨ hsame row E ∨
                                hsame row S ∨ hsame row A ∨ hsame row R ∨
                                  hsame row refusalRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont T C E ∧
                                Cont E S positiveRead ∧ Cont R Q refusalRead)
                            hsame ∧
                          UnaryHistory positiveRead ∧ UnaryHistory refusalRead ∧
                            Cont T C E ∧ Cont E S positiveRead ∧
                              Cont R Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert
  intro tUnary cUnary eUnary sUnary _aUnary rUnary qUnary candidateRoute positiveRoute
    refusalRoute
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed eUnary sUnary positiveRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed rUnary qUnary refusalRoute
  have sourceRefusal :
      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row) refusalRead := by
    exact ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row C ∨ hsame row E ∨ hsame row S ∨
              hsame row A ∨ hsame row R ∨ hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T C E ∧ Cont E S positiveRead ∧
              Cont R Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceRefusal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, candidateRoute, positiveRoute, refusalRoute⟩
  }
  exact ⟨cert, positiveUnary, refusalUnary, candidateRoute, positiveRoute, refusalRoute⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
