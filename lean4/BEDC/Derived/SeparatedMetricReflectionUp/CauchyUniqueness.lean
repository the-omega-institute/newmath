import BEDC.Derived.SeparatedMetricReflectionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SeparatedMetricReflectionCarrier_cauchy_uniqueness
    {X S A U Z H C P N zeroRead adjunctionRead universalRead leftRead rightRead : BHist} :
    Cont X S zeroRead ->
      Cont zeroRead A adjunctionRead ->
        Cont adjunctionRead U universalRead ->
          Cont universalRead H leftRead ->
            Cont universalRead H rightRead ->
              hsame leftRead rightRead ->
                UnaryHistory X ->
                  UnaryHistory S ->
                    UnaryHistory A ->
                      UnaryHistory U ->
                        UnaryHistory H ->
                          SemanticNameCert
                              (fun row : BHist => hsame row leftRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row X ∨ hsame row S ∨ hsame row A ∨
                                  hsame row U ∨ hsame row Z ∨ hsame row H ∨
                                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                                      hsame row leftRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont X S zeroRead ∧
                                  Cont zeroRead A adjunctionRead ∧
                                    Cont adjunctionRead U universalRead ∧
                                      Cont universalRead H leftRead)
                              hsame ∧
                            UnaryHistory zeroRead ∧ UnaryHistory adjunctionRead ∧
                              UnaryHistory universalRead ∧ UnaryHistory leftRead ∧
                                UnaryHistory rightRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro zeroRoute adjunctionRoute universalRoute leftRoute rightRoute sameReads
  intro xUnary sUnary aUnary uUnary hUnary
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed xUnary sUnary zeroRoute
  have adjunctionUnary : UnaryHistory adjunctionRead :=
    unary_cont_closed zeroUnary aUnary adjunctionRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed adjunctionUnary uUnary universalRoute
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed universalUnary hUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed universalUnary hUnary rightRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro leftRead ⟨hsame_refl leftRead, leftUnary⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr sourceRow.left))))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, zeroRoute, adjunctionRoute, universalRoute, leftRoute⟩
    }
  · exact ⟨zeroUnary, adjunctionUnary, universalUnary, leftUnary, rightUnary⟩

end BEDC.Derived.SeparatedMetricReflectionUp
