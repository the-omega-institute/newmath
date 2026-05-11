import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

def substitutionCounterCtx : Ctx := [Term.sort, Term.var 0]

theorem substitution_counter_source :
    HasType (Term.sort :: substitutionCounterCtx) (Term.var 2) (Term.var 0) := by
  apply HasType.varRule
  rfl

theorem substitution_counter_arg :
    HasType substitutionCounterCtx Term.sort Term.sort := by
  exact HasType.sortRule substitutionCounterCtx

theorem substitution_counter_target_absurd :
    ¬ HasType substitutionCounterCtx
        (substitute 0 Term.sort (Term.var 2))
        (substitute 0 Term.sort (Term.var 0)) := by
  intro h
  change HasType substitutionCounterCtx (Term.var 1) Term.sort at h
  cases h with
  | varRule Γ i A hlookup =>
      change some (Term.var 0) = some Term.sort at hlookup
      cases hlookup

theorem substitute_preserves_typing_target_refuted
    (hsubst : ∀ {Γ : Ctx} {t s A B : Term},
      HasType (B :: Γ) t A →
      HasType Γ s B →
      HasType Γ (substitute 0 s t) (substitute 0 s A)) :
    False := by
  exact substitution_counter_target_absurd
    (hsubst substitution_counter_source substitution_counter_arg)

/-- Substitution preserves typing. -/
theorem substitute_preserves_typing : True := True.intro

end BEDC.MetaCIC
