import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootClassifierBudgetLock
    {Z S M R Q H C P N classifierRead budgetRead lockedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S classifierRead ->
        Cont classifierRead H budgetRead ->
          Cont budgetRead Q lockedRead ->
            SemanticNameCert
                (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row H ∨
                    hsame row classifierRead ∨ hsame row budgetRead ∨
                      hsame row lockedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S classifierRead ∧
                    Cont classifierRead H budgetRead ∧ Cont budgetRead Q lockedRead ∧
                      hsame H (append Z S))
                hsame ∧
              UnaryHistory classifierRead ∧ UnaryHistory budgetRead ∧
                UnaryHistory lockedRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet classifierRoute budgetRoute lockedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryZ unaryS classifierRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed classifierUnary unaryH budgetRoute
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed budgetUnary unaryQ lockedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row Q ∨ hsame row H ∨
              hsame row classifierRead ∨ hsame row budgetRead ∨ hsame row lockedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S classifierRead ∧
              Cont classifierRead H budgetRead ∧ Cont budgetRead Q lockedRead ∧
                hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lockedRead ⟨hsame_refl lockedRead, lockedUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, budgetRoute, lockedRoute, sameH⟩
  }
  exact ⟨cert, classifierUnary, budgetUnary, lockedUnary, sameH⟩

theorem CriticalLineWitnessCarrier_root_classifier_budget_lock
    {Z S M R Q H C P N classifierRead budgetRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H classifierRead ->
        Cont N Q budgetRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
              UnaryHistory classifierRead ∧ UnaryHistory budgetRead ∧
                hsame H (append Z S) ∧ Cont Q H classifierRead ∧
                  Cont N Q budgetRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet classifierRoute budgetRoute
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
  have unaryClassifierRead : UnaryHistory classifierRead :=
    unary_cont_closed unaryQ unaryH classifierRoute
  have unaryBudgetRead : UnaryHistory budgetRead :=
    unary_cont_closed unaryN unaryQ budgetRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN,
      unaryClassifierRead, unaryBudgetRead, sameH, classifierRoute, budgetRoute,
      routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
