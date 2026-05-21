import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_finite_budget_source_totality
    {Z S M R Q H C P N budgetRead sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q budgetRead ->
        Cont budgetRead H sourceRead ->
          SemanticNameCert
              (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row sourceRead ∧ Cont (append Z S) Q budgetRead)
              (fun row : BHist => hsame row sourceRead ∧ Cont budgetRead H sourceRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory budgetRead ∧
                UnaryHistory sourceRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N ∧ Cont (append Z S) Q budgetRead ∧
                    Cont budgetRead H sourceRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet budgetRoute sourceRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have appendUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendUnary (hsame_symm sameH)
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed appendUnary unaryQ budgetRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed budgetUnary unaryH sourceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row sourceRead ∧ Cont (append Z S) Q budgetRead)
          (fun row : BHist => hsame row sourceRead ∧ Cont budgetRead H sourceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
      exact ⟨source.left, sourceRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, budgetUnary, sourceUnary,
      sameH, routeQ, routeC, routeN, budgetRoute, sourceRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
