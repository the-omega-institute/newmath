import BEDC.Derived.CauchyRateBudgetUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CauchyRateBudgetCarrier_rate_nonescape
    {R W Q D E H C P N rateWindow readbackTolerance sealRead : BHist} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory D ->
            UnaryHistory E ->
              Cont R W rateWindow ->
                Cont rateWindow Q readbackTolerance ->
                  Cont readbackTolerance D sealRead ->
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨
                            hsame row E ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont R W rateWindow ∧
                            Cont rateWindow Q readbackTolerance ∧
                              Cont readbackTolerance D sealRead)
                        hsame ∧
                      UnaryHistory rateWindow ∧ UnaryHistory readbackTolerance ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert
  intro rUnary wUnary qUnary dUnary _eUnary rateRoute toleranceRoute sealRoute
  have rateUnary : UnaryHistory rateWindow :=
    unary_cont_closed rUnary wUnary rateRoute
  have toleranceUnary : UnaryHistory readbackTolerance :=
    unary_cont_closed rateUnary qUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary dUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row E ∨
              hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W rateWindow ∧
              Cont rateWindow Q readbackTolerance ∧ Cont readbackTolerance D sealRead)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rateRoute, toleranceRoute, sealRoute⟩
  }
  exact ⟨cert, rateUnary, toleranceUnary, sealUnary⟩

theorem CauchyRateBudgetStreamNameRegSeqHandoff
    {R W Q D E H C P N rateWindow readbackTolerance sealRead : BHist} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory D ->
            UnaryHistory E ->
              Cont R W rateWindow ->
                Cont rateWindow Q readbackTolerance ->
                  Cont readbackTolerance D sealRead ->
                    SemanticNameCert
                        (fun row : BHist => hsame row readbackTolerance ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨
                            hsame row readbackTolerance)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont R W rateWindow ∧
                            Cont rateWindow Q readbackTolerance ∧
                              Cont readbackTolerance D sealRead)
                        hsame ∧
                      UnaryHistory rateWindow ∧ UnaryHistory readbackTolerance ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert
  intro rUnary wUnary qUnary dUnary _eUnary rateRoute toleranceRoute sealRoute
  have rateUnary : UnaryHistory rateWindow :=
    unary_cont_closed rUnary wUnary rateRoute
  have toleranceUnary : UnaryHistory readbackTolerance :=
    unary_cont_closed rateUnary qUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary dUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackTolerance ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row Q ∨ hsame row D ∨
              hsame row readbackTolerance)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W rateWindow ∧
              Cont rateWindow Q readbackTolerance ∧ Cont readbackTolerance D sealRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro readbackTolerance ⟨hsame_refl readbackTolerance, toleranceUnary⟩
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
      exact ⟨source.right, rateRoute, toleranceRoute, sealRoute⟩
  }
  exact ⟨cert, rateUnary, toleranceUnary, sealUnary⟩

end BEDC.Derived.CauchyRateBudgetUp
