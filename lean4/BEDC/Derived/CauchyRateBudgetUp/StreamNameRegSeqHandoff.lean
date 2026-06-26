import BEDC.Derived.CauchyRateBudgetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CauchyRateBudgetCarrier_streamname_regseq_handoff
    {R W Q D E H C P N rateWindow readbackRead toleranceRead : BHist} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory D ->
            Cont R W rateWindow ->
              Cont rateWindow Q readbackRead ->
                Cont readbackRead D toleranceRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨
                          hsame row readbackRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont R W rateWindow ∧
                          Cont rateWindow Q readbackRead ∧ Cont readbackRead D toleranceRead)
                      hsame ∧
                    cauchyRateBudgetFields (CauchyRateBudgetUp.mk R W Q D E H C P N) =
                      [R, W, Q, D, E, H, C, P, N] ∧
                      UnaryHistory rateWindow ∧ UnaryHistory readbackRead ∧
                        UnaryHistory toleranceRead := by
  -- BEDC touchpoint anchor: CauchyRateBudgetUp BHist Cont hsame SemanticNameCert
  intro rUnary wUnary qUnary dUnary rateRoute readbackRoute toleranceRoute
  have rateUnary : UnaryHistory rateWindow :=
    unary_cont_closed rUnary wUnary rateRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed rateUnary qUnary readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary dUnary toleranceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row readbackRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W rateWindow ∧ Cont rateWindow Q readbackRead ∧
              Cont readbackRead D toleranceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readbackRead ⟨hsame_refl readbackRead, readbackUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rateRoute, readbackRoute, toleranceRoute⟩
  }
  exact ⟨cert, rfl, rateUnary, readbackUnary, toleranceUnary⟩

end BEDC.Derived.CauchyRateBudgetUp
