import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_selector_budget_nonescape
    {Z S M R Q H C P N sourceWindow budgetRead regseqRoute realEndpoint refusalLedger
      selectorRead budgetLock : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceWindow ->
        Cont sourceWindow Q budgetRead ->
          Cont budgetRead R regseqRoute ->
            Cont regseqRoute H realEndpoint ->
              Cont realEndpoint N refusalLedger ->
                Cont refusalLedger C selectorRead ->
                  Cont selectorRead P budgetLock ->
                    SemanticNameCert
                        (fun row : BHist => hsame row budgetLock ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row sourceWindow ∨ hsame row budgetRead ∨
                            hsame row regseqRoute ∨ hsame row realEndpoint ∨
                              hsame row refusalLedger ∨ hsame row selectorRead ∨
                                hsame row budgetLock)
                        (fun row : BHist => UnaryHistory row ∧ Cont selectorRead P budgetLock)
                        hsame ∧ UnaryHistory budgetLock ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro carrier sourceRoute budgetRoute regseqRouteH realEndpointRoute refusalLedgerRoute
    selectorRoute budgetLockRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    carrier
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have sourceUnary : UnaryHistory sourceWindow :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed sourceUnary unaryQ budgetRoute
  have regseqUnary : UnaryHistory regseqRoute :=
    unary_cont_closed budgetUnary unaryR regseqRouteH
  have realUnary : UnaryHistory realEndpoint :=
    unary_cont_closed regseqUnary unaryH realEndpointRoute
  have refusalUnary : UnaryHistory refusalLedger :=
    unary_cont_closed realUnary unaryN refusalLedgerRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed refusalUnary unaryC selectorRoute
  have budgetLockUnary : UnaryHistory budgetLock :=
    unary_cont_closed selectorUnary unaryP budgetLockRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetLock ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceWindow ∨ hsame row budgetRead ∨ hsame row regseqRoute ∨
              hsame row realEndpoint ∨ hsame row refusalLedger ∨ hsame row selectorRead ∨
                hsame row budgetLock)
          (fun row : BHist => UnaryHistory row ∧ Cont selectorRead P budgetLock)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetLock ⟨hsame_refl budgetLock, budgetLockUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, budgetLockRoute⟩
  }
  exact ⟨cert, budgetLockUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
