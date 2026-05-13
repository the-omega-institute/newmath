import BEDC.MetaCIC.Confluence.AtomShape

namespace BEDC.MetaCIC

theorem betaStarStep_diamond_sort {t1 t2 : Term}
    (h1 : BetaStarStep Term.sort t1)
    (h2 : BetaStarStep Term.sort t2) :
    Exists (fun v => BetaStarStep t1 v ∧ BetaStarStep t2 v) := by
  exact betaStar_sort_join h1 h2

theorem betaStarStep_diamond_var {i : Idx} {t1 t2 : Term}
    (h1 : BetaStarStep (Term.var i) t1)
    (h2 : BetaStarStep (Term.var i) t2) :
    Exists (fun v => BetaStarStep t1 v ∧ BetaStarStep t2 v) := by
  exact betaStar_var_join i h1 h2

theorem betaParallel_pi_inv {d c t : Term}
    (h : BetaParallel (Term.pi d c) t) :
    ∃ d' c', t = Term.pi d' c' ∧ BetaParallel d d' ∧ BetaParallel c c' := by
  exact betaParallel_pi_shape h

theorem betaParallel_lam_inv {d b t : Term}
    (h : BetaParallel (Term.lam d b) t) :
    ∃ d' b', t = Term.lam d' b' ∧ BetaParallel d d' ∧ BetaParallel b b' := by
  exact betaParallel_lam_shape h

theorem betaParallel_app_target_shape {f a f' a' : Term}
    (h : BetaParallel (Term.app f a) (Term.app f' a')) :
    (BetaParallel f f' ∧ BetaParallel a a') ∨
    (∃ d body arg',
      BetaParallel f (Term.lam d body) ∧ BetaParallel a arg' ∧
        Term.app f' a' = substitute 0 arg' body) := by
  have hshape := betaParallel_app_shape h
  cases hshape with
  | inl hp =>
      cases hp with
      | intro g hg =>
          cases hg with
          | intro arg hpack =>
              cases hpack with
              | intro hf hrest =>
                  cases hrest with
                  | intro ha ht =>
                      cases ht
                      exact Or.inl (And.intro hf ha)
  | inr hredex =>
      exact Or.inr hredex

theorem betaParallel_app_no_beta {f a f' a' : Term}
    (h_not_lam : ∀ d b, ¬ BetaParallel f (Term.lam d b))
    (h : BetaParallel (Term.app f a) (Term.app f' a')) :
    BetaParallel f f' ∧ BetaParallel a a' := by
  have hshape := betaParallel_app_target_shape h
  cases hshape with
  | inl hp =>
      exact hp
  | inr hredex =>
      cases hredex with
      | intro d hd =>
          cases hd with
          | intro body hbody =>
              cases hbody with
              | intro arg' hpack =>
                  cases hpack with
                  | intro hf _ =>
                      exact False.elim (h_not_lam d body hf)

end BEDC.MetaCIC
