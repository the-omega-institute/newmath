import BEDC.Derived.RegularCauchyApartnessBudgetUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyApartnessBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyApartnessBudgetCarrier_lower_bound_scope
    {A M W D R budgetRead lowerRead readbackRead : BHist} :
    UnaryHistory A →
      UnaryHistory M →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory R →
              Cont A M budgetRead →
                Cont W D lowerRead →
                  Cont lowerRead R readbackRead →
                    SemanticNameCert
                        (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨
                            hsame row R ∨ hsame row lowerRead ∨ hsame row readbackRead)
                        (fun row : BHist =>
                          hsame row lowerRead ∧ Cont A M budgetRead ∧
                            Cont W D lowerRead ∧ Cont lowerRead R readbackRead)
                        hsame ∧
                      UnaryHistory budgetRead ∧ UnaryHistory lowerRead ∧
                        UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro aUnary mUnary wUnary dUnary rUnary budgetRoute lowerRoute readbackRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed aUnary mUnary budgetRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed wUnary dUnary lowerRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed lowerUnary rUnary readbackRoute
  have sourceLower :
      (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row) lowerRead :=
    ⟨hsame_refl lowerRead, lowerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row lowerRead ∨ hsame row readbackRead)
          (fun row : BHist =>
            hsame row lowerRead ∧ Cont A M budgetRead ∧ Cont W D lowerRead ∧
              Cont lowerRead R readbackRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lowerRead sourceLower
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, budgetRoute, lowerRoute, readbackRoute⟩
  }
  exact ⟨cert, budgetUnary, lowerUnary, readbackUnary⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
