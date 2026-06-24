import BEDC.Derived.EvenOddCauchyCriterionUp.Route

namespace BEDC.Derived.EvenOddCauchyCriterionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem EvenOddCauchyRealHandoffExhaustion
    {A B SA SB eps M D F R H C P N selected budgetRead toleranceRead fusionRead
      realRead : BHist} :
    EvenOddCauchyCriterionCarrier A B SA SB eps M D F R H C P N ->
      Cont eps SA selected ->
        Cont selected M budgetRead ->
          Cont budgetRead D toleranceRead ->
            Cont toleranceRead F fusionRead ->
              Cont fusionRead R realRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row eps ∨ hsame row M ∨ hsame row D ∨ hsame row F ∨
                        hsame row R ∨ hsame row realRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont eps SA selected ∧
                        Cont selected M budgetRead ∧ Cont budgetRead D toleranceRead ∧
                          Cont toleranceRead F fusionRead ∧ Cont fusionRead R realRead)
                    hsame ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: EvenOddCauchyCriterionCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier selectedRoute budgetRoute toleranceRoute fusionRoute realRoute
  obtain ⟨_aUnary, _bUnary, saUnary, _sbUnary, epsUnary, mUnary, dUnary, fUnary, rUnary,
    _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed epsUnary saUnary selectedRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed selectedUnary mUnary budgetRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed budgetUnary dUnary toleranceRoute
  have fusionUnary : UnaryHistory fusionRead :=
    unary_cont_closed toleranceUnary fUnary fusionRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed fusionUnary rUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row eps ∨ hsame row M ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
              hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont eps SA selected ∧ Cont selected M budgetRead ∧
              Cont budgetRead D toleranceRead ∧ Cont toleranceRead F fusionRead ∧
                Cont fusionRead R realRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
      exact ⟨source.right, selectedRoute, budgetRoute, toleranceRoute, fusionRoute, realRoute⟩
  }
  exact ⟨cert, realUnary⟩

end BEDC.Derived.EvenOddCauchyCriterionUp
