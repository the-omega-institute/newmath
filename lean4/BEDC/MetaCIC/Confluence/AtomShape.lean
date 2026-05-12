import BEDC.MetaCIC.Confluence.Core

namespace BEDC.MetaCIC

theorem betaStep_var_absurd
    (i : Idx) {u : Term} :
    BetaStep (Term.var i) u → False := by
  intro h
  cases h

theorem betaStep_sort_absurd
    {u : Term} :
    BetaStep Term.sort u → False := by
  intro h
  cases h

theorem betaStep_app_cases {f a t : Term}
    (h : BetaStep (Term.app f a) t) :
    (∃ d b, f = Term.lam d b ∧ t = substitute 0 a b) ∨
    (∃ f', BetaStep f f' ∧ t = Term.app f' a) ∨
    (∃ a', BetaStep a a' ∧ t = Term.app f a') := by
  cases h with
  | beta d b a =>
      exact Or.inl (Exists.intro d (Exists.intro b (And.intro rfl rfl)))
  | congApp1 f f' a hff' =>
      exact Or.inr (Or.inl (Exists.intro f' (And.intro hff' rfl)))
  | congApp2 f a a' haa' =>
      exact Or.inr (Or.inr (Exists.intro a' (And.intro haa' rfl)))

theorem betaStep_app_non_lam {f a t : Term}
    (h_not_lam : ∀ d b, f ≠ Term.lam d b)
    (hbeta : BetaStep (Term.app f a) t) :
    (∃ f', BetaStep f f' ∧ t = Term.app f' a) ∨
    (∃ a', BetaStep a a' ∧ t = Term.app f a') := by
  have hcases := betaStep_app_cases hbeta
  cases hcases with
  | inl hredex =>
      cases hredex with
      | intro d hd =>
          cases hd with
          | intro b hb =>
              cases hb with
              | intro hf ht =>
                  exact False.elim (h_not_lam d b hf)
  | inr hcong =>
      exact hcong

theorem betaStarStep_app_non_lam_shape_aux {s t f a : Term}
    (hs : s = Term.app f a)
    (h_not_lam : ∀ d b, ¬ BetaStarStep f (Term.lam d b))
    (h : BetaStarStep s t) :
    ∃ f' a', t = Term.app f' a' ∧ BetaStarStep f f' ∧ BetaStarStep a a' := by
  induction h generalizing f a with
  | refl s =>
      cases hs
      exact
        Exists.intro f
          (Exists.intro a
            (And.intro rfl
              (And.intro (BetaStarStep.refl f) (BetaStarStep.refl a))))
  | step hstep htail ih =>
      cases hs
      have hcases := betaStep_app_cases hstep
      cases hcases with
      | inl hredex =>
          cases hredex with
          | intro d hd =>
              cases hd with
              | intro b hb =>
                  cases hb with
                  | intro hf _ =>
                      cases hf
                      exact False.elim
                        (h_not_lam d b (BetaStarStep.refl (Term.lam d b)))
      | inr hcong =>
          cases hcong with
          | inl hfstep =>
              cases hfstep with
              | intro f1 hfpack =>
                  cases hfpack with
                  | intro hff1 ht =>
                      cases ht
                      have h_not_lam_f1 :
                          ∀ d b, ¬ BetaStarStep f1 (Term.lam d b) := by
                        intro d b hstar
                        exact h_not_lam d b (BetaStarStep.step hff1 hstar)
                      have htail_shape := ih rfl h_not_lam_f1
                      cases htail_shape with
                      | intro f2 hf2 =>
                          cases hf2 with
                          | intro a2 ha2 =>
                              cases ha2 with
                              | intro ht2 hstars =>
                                  cases hstars with
                                  | intro hf1f2 ha_a2 =>
                                      exact
                                        Exists.intro f2
                                          (Exists.intro a2
                                            (And.intro ht2
                                              (And.intro
                                                (BetaStarStep.step hff1 hf1f2)
                                                ha_a2)))
          | inr hasteps =>
              cases hasteps with
              | intro a1 hapack =>
                  cases hapack with
                  | intro haa1 ht =>
                      cases ht
                      have htail_shape := ih rfl h_not_lam
                      cases htail_shape with
                      | intro f2 hf2 =>
                          cases hf2 with
                          | intro a2 ha2 =>
                              cases ha2 with
                              | intro ht2 hstars =>
                                  cases hstars with
                                  | intro hf_f2 ha1a2 =>
                                      exact
                                        Exists.intro f2
                                          (Exists.intro a2
                                            (And.intro ht2
                                              (And.intro
                                                hf_f2
                                                (BetaStarStep.step haa1 ha1a2))))

theorem betaStarStep_app_non_lam_shape {f a t : Term}
    (h_not_lam : ∀ d b, ¬ BetaStarStep f (Term.lam d b))
    (h : BetaStarStep (Term.app f a) t) :
    ∃ f' a', t = Term.app f' a' ∧ BetaStarStep f f' ∧ BetaStarStep a a' := by
  exact betaStarStep_app_non_lam_shape_aux rfl h_not_lam h

theorem betaStep_pi_cases {d c t : Term}
    (h : BetaStep (Term.pi d c) t) :
    (∃ c', BetaStep c c' ∧ t = Term.pi d c') ∨
    (∃ d', BetaStep d d' ∧ t = Term.pi d' c) := by
  cases h with
  | congPiCod d c c' hc =>
      exact Or.inl (Exists.intro c' (And.intro hc rfl))
  | congPiDom d d' c hd =>
      exact Or.inr (Exists.intro d' (And.intro hd rfl))

theorem betaStep_lam_cases {d b t : Term}
    (h : BetaStep (Term.lam d b) t) :
    (∃ b', BetaStep b b' ∧ t = Term.lam d b') ∨
    (∃ d', BetaStep d d' ∧ t = Term.lam d' b) := by
  cases h with
  | congLam d b b' hb =>
      exact Or.inl (Exists.intro b' (And.intro hb rfl))
  | congLamDom d d' b hd =>
      exact Or.inr (Exists.intro d' (And.intro hd rfl))

theorem betaStep_pi_iff {d c t : Term} :
    BetaStep (Term.pi d c) t ↔
      (∃ c', BetaStep c c' ∧ t = Term.pi d c') ∨
      (∃ d', BetaStep d d' ∧ t = Term.pi d' c) := by
  constructor
  · intro h
    cases h with
    | congPiCod d c c' hc =>
        exact Or.inl (Exists.intro c' (And.intro hc rfl))
    | congPiDom d d' c hd =>
        exact Or.inr (Exists.intro d' (And.intro hd rfl))
  · intro h
    cases h with
    | inl hc =>
        cases hc with
        | intro c' hc' =>
            cases hc' with
            | intro hstep ht =>
                cases ht
                exact BetaStep.congPiCod d c c' hstep
    | inr hd =>
        cases hd with
        | intro d' hd' =>
            cases hd' with
            | intro hstep ht =>
                cases ht
                exact BetaStep.congPiDom d d' c hstep

theorem betaStep_lam_iff {d b t : Term} :
    BetaStep (Term.lam d b) t ↔
      (∃ b', BetaStep b b' ∧ t = Term.lam d b') ∨
      (∃ d', BetaStep d d' ∧ t = Term.lam d' b) := by
  constructor
  · intro h
    cases h with
    | congLam d b b' hb =>
        exact Or.inl (Exists.intro b' (And.intro hb rfl))
    | congLamDom d d' b hd =>
        exact Or.inr (Exists.intro d' (And.intro hd rfl))
  · intro h
    cases h with
    | inl hb =>
        cases hb with
        | intro b' hb' =>
            cases hb' with
            | intro hstep ht =>
                cases ht
                exact BetaStep.congLam d b b' hstep
    | inr hd =>
        cases hd with
        | intro d' hd' =>
            cases hd' with
            | intro hstep ht =>
                cases ht
                exact BetaStep.congLamDom d d' b hstep

theorem betaStep_source_not_sort {t : Term} :
    ¬ BetaStep Term.sort t := by
  exact betaStep_sort_absurd

theorem betaStep_source_not_var {i : Idx} {t : Term} :
    ¬ BetaStep (Term.var i) t := by
  exact betaStep_var_absurd i

theorem betaParallel_refl_self_atom {t : Term}
    (h : t = Term.sort ∨ ∃ i, t = Term.var i) :
    BetaParallel t t := by
  cases h with
  | inl hsort =>
      cases hsort
      exact BetaParallel.sort
  | inr hvar =>
      cases hvar with
      | intro i hi =>
          cases hi
          exact BetaParallel.var i

theorem betaStar_var_target
    (i : Idx) {u : Term}
    (h : BetaStarStep (Term.var i) u) :
    u = Term.var i := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_var_absurd i hstep)

theorem betaStarStep_var_refl_only {i : Idx} {t : Term}
    (h : BetaStarStep (Term.var i) t) :
    t = Term.var i := by
  exact betaStar_var_target i h

theorem betaStarStep_var_unique_target {i : Idx} {t : Term}
    (h : BetaStarStep (Term.var i) t) :
    t = Term.var i := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_var_absurd i hstep)

theorem betaStar_sort_target
    {u : Term}
    (h : BetaStarStep Term.sort u) :
    u = Term.sort := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_sort_absurd hstep)

theorem betaStarStep_sort_unique {t : Term}
    (h : BetaStarStep Term.sort t) :
    t = Term.sort := by
  exact betaStar_sort_target h

theorem betaStarStep_sort_unique_target {t : Term}
    (h : BetaStarStep Term.sort t) :
    t = Term.sort := by
  cases h with
  | refl t =>
      rfl
  | step hstep _ =>
      exact False.elim (betaStep_sort_absurd hstep)

theorem betaStarStep_atom_refl_only {t t' : Term}
    (hatom : t = Term.sort ∨ ∃ i, t = Term.var i)
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

theorem betaStarStep_atom_reflexive {t t' : Term}
    (hatom : t = Term.sort ∨ ∃ i, t = Term.var i)
    (h : BetaStarStep t t') :
    t = t' := by
  cases betaStarStep_atom_refl_only hatom h
  rfl

theorem betaParallel_betaStarStep_atom_coincide {t t' : Term}
    (hatom : t = Term.sort ∨ ∃ i, t = Term.var i)
    (h : BetaParallel t t') :
    t' = t ∧ BetaStarStep t t' := by
  exact
    And.intro
      (betaStarStep_atom_refl_only hatom (betaStarStep_of_betaParallel_atom hatom h))
      (betaStarStep_of_betaParallel_atom hatom h)

theorem betaStar_var_join
    (i : Idx) {u1 u2 : Term}
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
    {u1 u2 : Term}
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
