import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_fixed_strip_zeta_consumer_boundary
    {Z S M R Q H C P N budgetRead zetaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S budgetRead ->
        Cont budgetRead Q zetaRead ->
          SemanticNameCert
              (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row zetaRead)
              (fun row : BHist => hsame row zetaRead ∧ Cont budgetRead Q zetaRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory budgetRead ∧
              UnaryHistory zetaRead ∧ hsame H (append Z S) ∧ Cont Z S budgetRead ∧
                Cont budgetRead Q zetaRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet budgetRoute zetaRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have _unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryZ unaryS budgetRoute
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed budgetUnary unaryQ zetaRoute
  have sourceAtZeta : hsame zetaRead zetaRead ∧ UnaryHistory zetaRead :=
    ⟨hsame_refl zetaRead, zetaUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row zetaRead)
          (fun row : BHist => hsame row zetaRead ∧ Cont budgetRead Q zetaRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zetaRead sourceAtZeta
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, zetaRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, budgetUnary, zetaUnary, sameH, budgetRoute,
      zetaRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
