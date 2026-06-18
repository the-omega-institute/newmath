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

theorem RegularCauchyApartnessBudgetCarrier_reciprocal_window_boundary
    {X A M W D R E H C P N budgetRead lowerRead readbackRead sealRead : BHist} :
    UnaryHistory X →
      UnaryHistory A →
        UnaryHistory M →
          UnaryHistory W →
            UnaryHistory D →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory P →
                    hsame H (append X A) →
                      Cont A M budgetRead →
                        Cont W D lowerRead →
                          Cont lowerRead R readbackRead →
                            Cont R E sealRead →
                              Cont E H C →
                                Cont C P N →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row readbackRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row readbackRead ∧
                                          Cont A M budgetRead ∧ Cont W D lowerRead)
                                      (fun row : BHist =>
                                        hsame row readbackRead ∧
                                          Cont lowerRead R readbackRead)
                                      hsame ∧
                                    UnaryHistory budgetRead ∧
                                      UnaryHistory lowerRead ∧
                                        UnaryHistory readbackRead ∧
                                          UnaryHistory sealRead ∧
                                            hsame H (append X A) ∧ Cont E H C ∧
                                              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro _xUnary aUnary mUnary wUnary dUnary rUnary eUnary _pUnary sameHeader
    budgetRoute lowerRoute readbackRoute sealRoute sealToHeader headerToName
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed aUnary mUnary budgetRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed wUnary dUnary lowerRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed lowerUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readbackRead ∧ Cont A M budgetRead ∧
              Cont W D lowerRead)
          (fun row : BHist =>
            hsame row readbackRead ∧ Cont lowerRead R readbackRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro readbackRead ⟨hsame_refl readbackRead, readbackUnary⟩
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
      exact ⟨source.left, budgetRoute, lowerRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackRoute⟩
  }
  exact
    ⟨cert, budgetUnary, lowerUnary, readbackUnary, sealUnary, sameHeader,
      sealToHeader, headerToName⟩

end BEDC.Derived.RegularCauchyApartnessBudgetUp
