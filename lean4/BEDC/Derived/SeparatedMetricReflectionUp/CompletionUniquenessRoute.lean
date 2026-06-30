import BEDC.Derived.SeparatedMetricReflectionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SeparatedMetricReflectionCarrier_completion_uniqueness_route
    {X S A U Z H C P N zeroRead adjunctionRead universalRead uniquenessRead : BHist} :
    Cont X S zeroRead ->
      Cont zeroRead A adjunctionRead ->
        Cont adjunctionRead U universalRead ->
          Cont universalRead C uniquenessRead ->
            UnaryHistory X ->
              UnaryHistory S ->
                UnaryHistory A ->
                  UnaryHistory U ->
                    UnaryHistory C ->
                      SemanticNameCert
                          (fun row : BHist => hsame row uniquenessRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row S ∨ hsame row A ∨ hsame row U ∨ hsame row Z ∨
                              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                                hsame row uniquenessRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont X S zeroRead ∧
                              Cont zeroRead A adjunctionRead ∧
                                Cont adjunctionRead U universalRead ∧
                                  Cont universalRead C uniquenessRead)
                          hsame ∧
                        UnaryHistory zeroRead ∧ UnaryHistory adjunctionRead ∧
                          UnaryHistory universalRead ∧ UnaryHistory uniquenessRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert NameCert
  intro zeroRoute adjunctionRoute universalRoute uniquenessRoute xUnary sUnary aUnary uUnary cUnary
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed xUnary sUnary zeroRoute
  have adjunctionUnary : UnaryHistory adjunctionRead :=
    unary_cont_closed zeroUnary aUnary adjunctionRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed adjunctionUnary uUnary universalRoute
  have uniquenessUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed universalUnary cUnary uniquenessRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro uniquenessRead ⟨hsame_refl uniquenessRead, uniquenessUnary⟩
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
          sourceRow.left)))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.right, zeroRoute, adjunctionRoute, universalRoute, uniquenessRoute⟩
    }
  · exact ⟨zeroUnary, adjunctionUnary, universalUnary, uniquenessUnary⟩

end BEDC.Derived.SeparatedMetricReflectionUp
