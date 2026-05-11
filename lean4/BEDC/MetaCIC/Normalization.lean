import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.ClosedTerm
import BEDC.MetaCIC.Typing

namespace BEDC.MetaCIC

theorem sort_no_beta {t : Term} : ¬ BetaStep Term.sort t := by
  intro h
  cases h

theorem closed_var_no_beta {i : Idx} {t : Term} : ¬ BetaStep (Term.var i) t := by
  intro h
  cases h

theorem closed_atom_normal_form {Γ : Ctx} {t : Term}
    (_hclosed : ClosedAt 0 t)
    (_ht : HasType Γ t Term.sort)
    (h_atom : t = Term.sort ∨ ∃ i, t = Term.var i)
    : ¬ ∃ t', BetaStep t t' := by
  intro hstep
  cases hstep with
  | intro t' hbeta =>
      cases h_atom with
      | inl hsort =>
          rw [hsort] at hbeta
          exact sort_no_beta hbeta
      | inr hvar =>
          cases hvar with
          | intro i hi =>
              rw [hi] at hbeta
              exact closed_var_no_beta hbeta

end BEDC.MetaCIC
