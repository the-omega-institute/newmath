import BEDC.MetaCIC.Confluence

namespace BEDC.MetaCIC


theorem betaStarStep_sort_unique_target {t : BEDC.MetaCIC.Term}
    (h : BetaStarStep Term.sort t) :
    t = Term.sort := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_sort_absurd hstep)

theorem betaStarStep_atom_refl_only {t t' : BEDC.MetaCIC.Term}
    (hatom : t = BEDC.MetaCIC.Term.sort ∨ ∃ i, t = BEDC.MetaCIC.Term.var i)
    (h : BetaStarStep t t') :
    t' = t := by
  cases hatom with
  | inl hsort =>
      cases hsort
      exact betaStar_sort_target h
  | inr hvar =>
      cases hvar with
      | intro i hi =>
          cases hi
          exact betaStar_var_target i h

theorem betaStarStep_atom_reflexive {t t' : BEDC.MetaCIC.Term}
    (hatom : t = BEDC.MetaCIC.Term.sort ∨ ∃ i, t = BEDC.MetaCIC.Term.var i)
    (h : BetaStarStep t t') :
    t = t' := by
  cases betaStarStep_atom_refl_only hatom h
  rfl

theorem betaParallel_betaStarStep_atom_coincide {t t' : BEDC.MetaCIC.Term}
    (hatom : t = BEDC.MetaCIC.Term.sort ∨ ∃ i, t = BEDC.MetaCIC.Term.var i)
    (h : BetaParallel t t') :
    t' = t ∧ BetaStarStep t t' := by
  exact
    And.intro
      (betaStarStep_atom_refl_only hatom (betaStarStep_of_betaParallel_atom hatom h))
      (betaStarStep_of_betaParallel_atom hatom h)

theorem betaStar_var_join
    (i : Idx) {u1 u2 : BEDC.MetaCIC.Term}
    (h1 : BetaStarStep (Term.var i) u1)
    (h2 : BetaStarStep (Term.var i) u2) :
    Exists (fun v => BetaStarStep u1 v ∧ BetaStarStep u2 v) := by
  cases betaStar_var_target i h1
  cases betaStar_var_target i h2
  exact
    Exists.intro
      (Term.var i)
      (And.intro
        (BetaStarStep.refl (Term.var i))
        (BetaStarStep.refl (Term.var i)))

theorem betaStar_sort_join
    {u1 u2 : BEDC.MetaCIC.Term}
    (h1 : BetaStarStep Term.sort u1)
    (h2 : BetaStarStep Term.sort u2) :
    Exists (fun v => BetaStarStep u1 v ∧ BetaStarStep u2 v) := by
  cases betaStar_sort_target h1
  cases betaStar_sort_target h2
  exact
    Exists.intro
      Term.sort
      (And.intro
        (BetaStarStep.refl Term.sort)
        (BetaStarStep.refl Term.sort))


end BEDC.MetaCIC
