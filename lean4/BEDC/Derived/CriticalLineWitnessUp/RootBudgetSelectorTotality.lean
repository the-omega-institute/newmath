import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_budget_selector_totality
    {Z S M R Q H C P N budgetRead selectorRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q budgetRead ->
        Cont budgetRead N selectorRead ->
          SemanticNameCert
              (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row selectorRead ∧ Cont (append Z S) Q budgetRead)
              (fun row : BHist => hsame row selectorRead ∧ Cont budgetRead N selectorRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory N ∧ UnaryHistory budgetRead ∧
                UnaryHistory selectorRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N ∧ Cont (append Z S) Q budgetRead ∧
                    Cont budgetRead N selectorRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet budgetRoute selectorRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
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
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed appendUnary unaryQ budgetRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed budgetUnary unaryN selectorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row selectorRead ∧ Cont (append Z S) Q budgetRead)
          (fun row : BHist => hsame row selectorRead ∧ Cont budgetRead N selectorRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro selectorRead ⟨hsame_refl selectorRead, selectorUnary⟩
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
      exact ⟨source.left, selectorRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryN, budgetUnary,
      selectorUnary, sameH, routeQ, routeC, routeN, budgetRoute, selectorRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
