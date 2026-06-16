import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SeparatedMetricReflectionCarrier_scoped_dependency_route
    {X S A U Z H C P N zeroRead adjunctionRead universalRead provenanceRead : BHist} :
    Cont X S zeroRead ->
      Cont zeroRead A adjunctionRead ->
        Cont adjunctionRead U universalRead ->
          Cont H C provenanceRead ->
            UnaryHistory X ->
              UnaryHistory S ->
                UnaryHistory A ->
                  UnaryHistory U ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        SemanticNameCert
                            (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row X ∨ hsame row S ∨ hsame row A ∨ hsame row U ∨
                                hsame row Z ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                                  hsame row N ∨ hsame row universalRead)
                            (fun row : BHist =>
                              hsame row universalRead ∧ Cont X S zeroRead ∧
                                Cont zeroRead A adjunctionRead ∧
                                  Cont adjunctionRead U universalRead ∧
                                    Cont H C provenanceRead)
                            hsame ∧
                          UnaryHistory zeroRead ∧ UnaryHistory adjunctionRead ∧
                            UnaryHistory universalRead ∧ UnaryHistory provenanceRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro zeroRoute adjunctionRoute universalRoute provenanceRoute xUnary sUnary aUnary uUnary
    hUnary cUnary
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed xUnary sUnary zeroRoute
  have adjunctionUnary : UnaryHistory adjunctionRead :=
    unary_cont_closed zeroUnary aUnary adjunctionRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed adjunctionUnary uUnary universalRoute
  have provenanceUnary : UnaryHistory provenanceRead :=
    unary_cont_closed hUnary cUnary provenanceRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro universalRead ⟨hsame_refl universalRead, universalUnary⟩
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
        exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr sourceRow.left))))))))
      ledger_sound := by
        intro _row sourceRow
        exact
          ⟨sourceRow.left, zeroRoute, adjunctionRoute, universalRoute, provenanceRoute⟩
    }
  · exact ⟨zeroUnary, adjunctionUnary, universalUnary, provenanceUnary⟩

end BEDC.Derived.SeparatedMetricReflectionUp
