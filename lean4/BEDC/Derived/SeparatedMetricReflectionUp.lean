import BEDC.Derived.SeparatedMetricReflectionUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SeparatedMetricReflectionNameCertObligations
    {X S A U Z H C P N zeroRead adjunctionRead universalRead : BHist} :
    Cont X S zeroRead →
      Cont zeroRead A adjunctionRead →
        Cont adjunctionRead U universalRead →
          UnaryHistory X →
            UnaryHistory S →
              UnaryHistory A →
                UnaryHistory U →
                  SemanticNameCert
                      (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
                      (fun row : BHist => hsame row universalRead)
                      (fun row : BHist => hsame row universalRead ∧
                        Cont adjunctionRead U universalRead)
                      hsame ∧
                    UnaryHistory zeroRead ∧ UnaryHistory adjunctionRead ∧
                      UnaryHistory universalRead ∧ hsame Z Z ∧ Cont X S zeroRead ∧
                        Cont zeroRead A adjunctionRead ∧ Cont adjunctionRead U universalRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert NameCert
  intro zeroRoute adjunctionRoute universalRoute xUnary sUnary aUnary uUnary
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed xUnary sUnary zeroRoute
  have adjunctionUnary : UnaryHistory adjunctionRead :=
    unary_cont_closed zeroUnary aUnary adjunctionRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed adjunctionUnary uUnary universalRoute
  have sourceUniversal :
      hsame universalRead universalRead ∧ UnaryHistory universalRead :=
    ⟨hsame_refl universalRead, universalUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row universalRead)
        (fun row : BHist => hsame row universalRead ∧
          Cont adjunctionRead U universalRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro universalRead sourceUniversal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.left, universalRoute⟩
    }
  exact
    ⟨cert, zeroUnary, adjunctionUnary, universalUnary, hsame_refl Z, zeroRoute,
      adjunctionRoute, universalRoute⟩

theorem SeparatedMetricReflectionCarrier_obligation_closure_package
    {X S A U Z H C P N zeroRead adjunctionRead universalRead : BHist} :
    Cont X S zeroRead ->
      Cont zeroRead A adjunctionRead ->
        Cont adjunctionRead U universalRead ->
          UnaryHistory X ->
            UnaryHistory S ->
              UnaryHistory A ->
                UnaryHistory U ->
                  SemanticNameCert
                      (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row S ∨ hsame row A ∨ hsame row U ∨
                          hsame row Z ∨ hsame row universalRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont X S zeroRead ∧
                          Cont zeroRead A adjunctionRead ∧
                            Cont adjunctionRead U universalRead)
                      hsame ∧
                    UnaryHistory zeroRead ∧ UnaryHistory adjunctionRead ∧
                      UnaryHistory universalRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame SemanticNameCert NameCert
  intro zeroRoute adjunctionRoute universalRoute xUnary sUnary aUnary uUnary
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed xUnary sUnary zeroRoute
  have adjunctionUnary : UnaryHistory adjunctionRead :=
    unary_cont_closed zeroUnary aUnary adjunctionRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed adjunctionUnary uUnary universalRoute
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, zeroRoute, adjunctionRoute, universalRoute⟩
    }
  · exact ⟨zeroUnary, adjunctionUnary, universalUnary⟩

end BEDC.Derived.SeparatedMetricReflectionUp
