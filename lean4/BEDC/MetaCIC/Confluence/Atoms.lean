import BEDC.MetaCIC.Confluence

namespace BEDC.MetaCIC

theorem betaStar_var_target
    (i : Idx) {u : BEDC.MetaCIC.Term}
    (h : BetaStarStep (BEDC.MetaCIC.Term.var i) u) :
    u = BEDC.MetaCIC.Term.var i := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_var_absurd i hstep)

theorem betaStarStep_var_refl_only {i : Idx} {t : BEDC.MetaCIC.Term}
    (h : BetaStarStep (BEDC.MetaCIC.Term.var i) t) :
    t = BEDC.MetaCIC.Term.var i := by
  exact betaStar_var_target i h

theorem betaStarStep_var_unique_target {i : Idx} {t : BEDC.MetaCIC.Term}
    (h : BetaStarStep (BEDC.MetaCIC.Term.var i) t) :
    t = BEDC.MetaCIC.Term.var i := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_var_absurd i hstep)

theorem betaStar_sort_target
    {u : BEDC.MetaCIC.Term}
    (h : BetaStarStep BEDC.MetaCIC.Term.sort u) :
    u = BEDC.MetaCIC.Term.sort := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_sort_absurd hstep)

theorem betaStarStep_sort_unique {t : BEDC.MetaCIC.Term}
    (h : BetaStarStep BEDC.MetaCIC.Term.sort t) :
    t = BEDC.MetaCIC.Term.sort := by
  exact betaStar_sort_target h

theorem betaStarStep_sort_unique_target {t : BEDC.MetaCIC.Term}
    (h : BetaStarStep BEDC.MetaCIC.Term.sort t) :
    t = BEDC.MetaCIC.Term.sort := by
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
    (h1 : BetaStarStep (BEDC.MetaCIC.Term.var i) u1)
    (h2 : BetaStarStep (BEDC.MetaCIC.Term.var i) u2) :
    Exists (fun v => BetaStarStep u1 v ∧ BetaStarStep u2 v) := by
  cases betaStar_var_target i h1
  cases betaStar_var_target i h2
  exact
    Exists.intro
      (BEDC.MetaCIC.Term.var i)
      (And.intro
        (BetaStarStep.refl (BEDC.MetaCIC.Term.var i))
        (BetaStarStep.refl (BEDC.MetaCIC.Term.var i)))

theorem betaStar_sort_join
    {u1 u2 : BEDC.MetaCIC.Term}
    (h1 : BetaStarStep BEDC.MetaCIC.Term.sort u1)
    (h2 : BetaStarStep BEDC.MetaCIC.Term.sort u2) :
    Exists (fun v => BetaStarStep u1 v ∧ BetaStarStep u2 v) := by
  cases betaStar_sort_target h1
  cases betaStar_sort_target h2
  exact
    Exists.intro
      BEDC.MetaCIC.Term.sort
      (And.intro
        (BetaStarStep.refl BEDC.MetaCIC.Term.sort)
        (BetaStarStep.refl BEDC.MetaCIC.Term.sort))

end BEDC.MetaCIC
