import BEDC.Derived.RegularCauchyTelescopingBudgetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTelescopingBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyTelescopingBudgetCarrier_window_chain
    {E W D R S T H C P N precisionRead ledgerRead telescopingRead handoffRead : BHist} :
    UnaryHistory E ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory T ->
            UnaryHistory R ->
              Cont E W precisionRead ->
                Cont precisionRead D ledgerRead ->
                  Cont ledgerRead T telescopingRead ->
                    Cont telescopingRead R handoffRead ->
                      SemanticNameCert
                          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row E ∨ hsame row W ∨ hsame row D ∨ hsame row T ∨
                              hsame row R ∨ hsame row handoffRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont E W precisionRead ∧
                              Cont precisionRead D ledgerRead ∧
                                Cont ledgerRead T telescopingRead ∧
                                  Cont telescopingRead R handoffRead)
                          hsame ∧
                        UnaryHistory precisionRead ∧ UnaryHistory ledgerRead ∧
                          UnaryHistory telescopingRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert
  intro eUnary wUnary dUnary tUnary rUnary precisionRoute ledgerRoute telescopingRoute
    handoffRoute
  have precisionUnary : UnaryHistory precisionRead :=
    unary_cont_closed eUnary wUnary precisionRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed precisionUnary dUnary ledgerRoute
  have telescopingUnary : UnaryHistory telescopingRead :=
    unary_cont_closed ledgerUnary tUnary telescopingRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed telescopingUnary rUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row W ∨ hsame row D ∨ hsame row T ∨ hsame row R ∨
              hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E W precisionRead ∧ Cont precisionRead D ledgerRead ∧
              Cont ledgerRead T telescopingRead ∧ Cont telescopingRead R handoffRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, precisionRoute, ledgerRoute, telescopingRoute, handoffRoute⟩
  }
  exact ⟨cert, precisionUnary, ledgerUnary, telescopingUnary, handoffUnary⟩

end BEDC.Derived.RegularCauchyTelescopingBudgetUp
