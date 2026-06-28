import BEDC.Derived.RegularCauchyTelescopingBudgetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTelescopingBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RegularCauchyTelescopingBudgetCarrier_bridge_route
    {E W D R S T H C P N precisionRead ledgerRead telescopingRead handoffRead sealRead
      bridgeRead : BHist} :
    UnaryHistory E ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory T ->
            UnaryHistory R ->
              UnaryHistory S ->
                UnaryHistory H ->
                  Cont E W precisionRead ->
                    Cont precisionRead D ledgerRead ->
                      Cont ledgerRead T telescopingRead ->
                        Cont telescopingRead R handoffRead ->
                          Cont handoffRead S sealRead ->
                            Cont sealRead H bridgeRead ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row bridgeRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row E ∨ hsame row W ∨ hsame row D ∨
                                      hsame row T ∨ hsame row R ∨ hsame row S ∨
                                        hsame row H ∨ hsame row bridgeRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont E W precisionRead ∧
                                      Cont precisionRead D ledgerRead ∧
                                        Cont ledgerRead T telescopingRead ∧
                                          Cont telescopingRead R handoffRead ∧
                                            Cont handoffRead S sealRead ∧
                                              Cont sealRead H bridgeRead)
                                  hsame ∧
                                UnaryHistory precisionRead ∧ UnaryHistory ledgerRead ∧
                                  UnaryHistory telescopingRead ∧ UnaryHistory handoffRead ∧
                                    UnaryHistory sealRead ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: RegularCauchyTelescopingBudgetUp BHist Cont hsame SemanticNameCert
  intro eUnary wUnary dUnary tUnary rUnary sUnary hUnary precisionRoute ledgerRoute
    telescopingRoute handoffRoute sealRoute bridgeRoute
  have precisionUnary : UnaryHistory precisionRead :=
    unary_cont_closed eUnary wUnary precisionRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed precisionUnary dUnary ledgerRoute
  have telescopingUnary : UnaryHistory telescopingRead :=
    unary_cont_closed ledgerUnary tUnary telescopingRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed telescopingUnary rUnary handoffRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffUnary sUnary sealRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed sealUnary hUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row W ∨ hsame row D ∨ hsame row T ∨ hsame row R ∨
              hsame row S ∨ hsame row H ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E W precisionRead ∧ Cont precisionRead D ledgerRead ∧
              Cont ledgerRead T telescopingRead ∧ Cont telescopingRead R handoffRead ∧
                Cont handoffRead S sealRead ∧ Cont sealRead H bridgeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
          source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, precisionRoute, ledgerRoute, telescopingRoute, handoffRoute,
          sealRoute, bridgeRoute⟩
  }
  exact
    ⟨cert, precisionUnary, ledgerUnary, telescopingUnary, handoffUnary, sealUnary,
      bridgeUnary⟩

end BEDC.Derived.RegularCauchyTelescopingBudgetUp
