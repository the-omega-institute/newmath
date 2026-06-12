import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessFixedStripZetaConsumerSeparation
    {Z S M R Q H C P N sourceRead budgetRead zetaRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R budgetRead ->
          Cont budgetRead Q zetaRead ->
            SemanticNameCert
                (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row zetaRead ∧ Cont Z S sourceRead)
                (fun row : BHist =>
                  hsame row zetaRead ∧ Cont M R budgetRead ∧
                    Cont budgetRead Q zetaRead)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory budgetRead ∧
                UnaryHistory zetaRead ∧ Cont Z S sourceRead ∧ Cont M R budgetRead ∧
                  Cont budgetRead Q zetaRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute budgetRoute zetaRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed unaryM unaryR budgetRoute
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed budgetUnary unaryQ zetaRoute
  have sourceAtZeta : hsame zetaRead zetaRead ∧ UnaryHistory zetaRead :=
    ⟨hsame_refl zetaRead, zetaUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zetaRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row zetaRead ∧ Cont Z S sourceRead)
          (fun row : BHist =>
            hsame row zetaRead ∧ Cont M R budgetRead ∧ Cont budgetRead Q zetaRead)
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
      exact ⟨source.left, sourceRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, budgetRoute, zetaRoute⟩
  }
  exact ⟨cert, sourceUnary, budgetUnary, zetaUnary, sourceRoute, budgetRoute, zetaRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
