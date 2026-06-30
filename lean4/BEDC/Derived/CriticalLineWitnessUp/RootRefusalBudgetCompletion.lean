import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_refusal_budget_completion
    {Z S M R Q H C P N rootRead rhRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q rootRead ->
        Cont rootRead N rhRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
            UnaryHistory rootRead ∧ UnaryHistory rhRead ∧ hsame H (append Z S) ∧
              Cont (append Z S) Q rootRead ∧ Cont rootRead N rhRead ∧ Cont M R Q ∧
                Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet rootRoute rhRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary routeClosure.left rootRoute
  have rhUnary : UnaryHistory rhRead :=
    unary_cont_closed rootUnary routeClosure.right.right.left rhRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, routeClosure.right.right.left, rootUnary, rhUnary,
      routeClosure.right.right.right, rootRoute, rhRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessRootRefusalBudgetExhaustion
    {Z S M R Q H C P N budgetRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S budgetRead ->
        Cont N Q refusalRead ->
          SemanticNameCert
              (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row refusalRead ∧ Cont Z S budgetRead)
              (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
              hsame ∧
            UnaryHistory budgetRead ∧ UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
              Cont Z S budgetRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                Cont N Q refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet budgetRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryZ unaryS budgetRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusalRead ∧ Cont Z S budgetRead)
          (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
      exact ⟨source.left, budgetRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨cert, budgetUnary, refusalUnary, sameH, budgetRoute, routeQ, routeC, routeN,
      refusalRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
