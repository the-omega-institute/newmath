import BEDC.Derived.CauchyRateBudgetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CauchyRateBudgetRealSealRouting
    {R W Q D E _H _C _P _N rateWindow readbackRead toleranceRead sealRead : BHist} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory D ->
            UnaryHistory E ->
              Cont R W rateWindow ->
                Cont rateWindow Q readbackRead ->
                  Cont readbackRead D toleranceRead ->
                    Cont toleranceRead E sealRead ->
                      SemanticNameCert
                          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨
                              hsame row E ∨ hsame row sealRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont R W rateWindow ∧
                              Cont rateWindow Q readbackRead ∧
                                Cont readbackRead D toleranceRead ∧
                                  Cont toleranceRead E sealRead)
                          hsame ∧
                        UnaryHistory rateWindow ∧ UnaryHistory readbackRead ∧
                          UnaryHistory toleranceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro rUnary wUnary qUnary dUnary eUnary rateRoute readbackRoute toleranceRoute sealRoute
  have rateUnary : UnaryHistory rateWindow :=
    unary_cont_closed rUnary wUnary rateRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed rateUnary qUnary readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary dUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
              hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W rateWindow ∧ Cont rateWindow Q readbackRead ∧
              Cont readbackRead D toleranceRead ∧ Cont toleranceRead E sealRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rateRoute, readbackRoute, toleranceRoute, sealRoute⟩
  }
  exact ⟨cert, rateUnary, readbackUnary, toleranceUnary, sealUnary⟩

end BEDC.Derived.CauchyRateBudgetUp
