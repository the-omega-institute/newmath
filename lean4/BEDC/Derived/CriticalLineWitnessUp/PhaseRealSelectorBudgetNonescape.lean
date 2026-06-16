import BEDC.Derived.CriticalLineWitnessUp.PhaseRealSelectorRoute

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_selector_budget_nonescape
    {Z S M R Q H C P N sourceWindow budgetRead regseqRoute realEndpoint refusalLedger
      selectorRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceWindow →
        Cont sourceWindow Q budgetRead →
          Cont budgetRead R regseqRoute →
            Cont regseqRoute H realEndpoint →
              Cont realEndpoint N refusalLedger →
                Cont refusalLedger C selectorRead →
                  SemanticNameCert
                      (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                          hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row sourceWindow ∨ hsame row budgetRead ∨
                              hsame row regseqRoute ∨ hsame row realEndpoint ∨
                                hsame row refusalLedger ∨ hsame row selectorRead)
                      (fun row : BHist =>
                        hsame row selectorRead ∧ Cont sourceWindow Q budgetRead ∧
                          Cont budgetRead R regseqRoute ∧ Cont regseqRoute H realEndpoint ∧
                            Cont realEndpoint N refusalLedger ∧
                              Cont refusalLedger C selectorRead)
                      hsame ∧
                    UnaryHistory sourceWindow ∧ UnaryHistory budgetRead ∧
                      UnaryHistory refusalLedger ∧ UnaryHistory selectorRead ∧
                        hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute budgetRoute regseqRouteRow realRoute refusalRoute selectorRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceWindow :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed sourceUnary unaryQ budgetRoute
  have regseqUnary : UnaryHistory regseqRoute :=
    unary_cont_closed budgetUnary unaryR regseqRouteRow
  have realUnary : UnaryHistory realEndpoint :=
    unary_cont_closed regseqUnary unaryH realRoute
  have refusalUnary : UnaryHistory refusalLedger :=
    unary_cont_closed realUnary unaryN refusalRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed refusalUnary unaryC selectorRoute
  have sourceAtSelector : hsame selectorRead selectorRead ∧ UnaryHistory selectorRead :=
    ⟨hsame_refl selectorRead, selectorUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row sourceWindow ∨ hsame row budgetRead ∨ hsame row regseqRoute ∨
                  hsame row realEndpoint ∨ hsame row refusalLedger ∨ hsame row selectorRead)
          (fun row : BHist =>
            hsame row selectorRead ∧ Cont sourceWindow Q budgetRead ∧
              Cont budgetRead R regseqRoute ∧ Cont regseqRoute H realEndpoint ∧
                Cont realEndpoint N refusalLedger ∧ Cont refusalLedger C selectorRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectorRead sourceAtSelector
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, budgetRoute, regseqRouteRow, realRoute, refusalRoute, selectorRoute⟩
  }
  exact ⟨cert, sourceUnary, budgetUnary, refusalUnary, selectorUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
