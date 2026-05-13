import BEDC.MetaCIC.Confluence.Diamond
import BEDC.MetaCIC.ClosurePreservation
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

def BetaNormal (t : Term) : Prop :=
  ∀ {u : Term}, BetaStep t u → False

theorem betaNormal_app_left {f a : Term}
    (h : BetaNormal (Term.app f a)) :
    BetaNormal f := by
  intro u hstep
  exact h (BetaStep.congApp1 f u a hstep)

theorem betaNormal_app_right {f a : Term}
    (h : BetaNormal (Term.app f a)) :
    BetaNormal a := by
  intro u hstep
  exact h (BetaStep.congApp2 f a u hstep)

theorem betaNormal_lam_domain {d b : Term}
    (h : BetaNormal (Term.lam d b)) :
    BetaNormal d := by
  intro u hstep
  exact h (BetaStep.congLamDom d u b hstep)

theorem betaNormal_lam_body {d b : Term}
    (h : BetaNormal (Term.lam d b)) :
    BetaNormal b := by
  intro u hstep
  exact h (BetaStep.congLam d b u hstep)

theorem betaNormal_pi_domain {d c : Term}
    (h : BetaNormal (Term.pi d c)) :
    BetaNormal d := by
  intro u hstep
  exact h (BetaStep.congPiDom d u c hstep)

theorem betaNormal_pi_codomain {d c : Term}
    (h : BetaNormal (Term.pi d c)) :
    BetaNormal c := by
  intro u hstep
  exact h (BetaStep.congPiCod d c u hstep)

theorem betaNormal_app_not_lam {f a d b : Term}
    (h : BetaNormal (Term.app f a))
    (heq : f = Term.lam d b) :
    False := by
  cases heq
  exact h (BetaStep.beta d b a)

theorem betaNormal_sort :
    BetaNormal Term.sort := by
  intro u hstep
  cases hstep

theorem betaParallel_preserves_closed {n : Idx} {t u : Term}
    (hclosed : ClosedAt n t)
    (h : BetaParallel t u) :
    ClosedAt n u := by
  induction h generalizing n with
  | var i =>
      exact hclosed
  | sort =>
      exact hclosed
  | app hf ha ihf iha =>
      cases hclosed with
      | appClosed hcf hca =>
          apply ClosedAt.appClosed
          · exact ihf hcf
          · exact iha hca
  | lam hd hb ihd ihb =>
      cases hclosed with
      | lamClosed hcd hcb =>
          apply ClosedAt.lamClosed
          · exact ihd hcd
          · exact ihb hcb
  | pi hd hc ihd ihc =>
      cases hclosed with
      | piClosed hcd hcc =>
          apply ClosedAt.piClosed
          · exact ihd hcd
          · exact ihc hcc
  | beta hd hb ha ihd ihb iha =>
      cases hclosed with
      | appClosed hfun harg =>
          cases hfun with
          | lamClosed hdom hbody =>
              exact
                substitute_preserves_closed_at
                  (Nat.zero_le n)
                  (iha harg)
                  (ihb hbody)
  | appBeta hf ha ihf iha =>
      cases hclosed with
      | appClosed hfun harg =>
          have hlamClosed := ihf hfun
          cases hlamClosed with
          | lamClosed _ hbody =>
              exact
                substitute_preserves_closed_at
                  (Nat.zero_le n)
                  (iha harg)
                  hbody

theorem betaParallel_preserves_closed_zero {t u : Term}
    (hclosed : ClosedAt 0 t)
    (h : BetaParallel t u) :
    ClosedAt 0 u := by
  exact betaParallel_preserves_closed hclosed h

theorem betaParallel_lam_target_body_closed {n : Idx} {t d b : Term}
    (hclosed : ClosedAt n t)
    (h : BetaParallel t (Term.lam d b)) :
    ClosedAt (n + 1) b := by
  have htarget := betaParallel_preserves_closed hclosed h
  cases htarget with
  | lamClosed _ hbody =>
      exact hbody

theorem betaParallel_lam_target_domain_closed {n : Idx} {t d b : Term}
    (hclosed : ClosedAt n t)
    (h : BetaParallel t (Term.lam d b)) :
    ClosedAt n d := by
  have htarget := betaParallel_preserves_closed hclosed h
  cases htarget with
  | lamClosed hdom _ =>
      exact hdom

theorem betaParallel_pi_target_codomain_closed {n : Idx} {t d c : Term}
    (hclosed : ClosedAt n t)
    (h : BetaParallel t (Term.pi d c)) :
    ClosedAt (n + 1) c := by
  have htarget := betaParallel_preserves_closed hclosed h
  cases htarget with
  | piClosed _ hcod =>
      exact hcod

theorem betaParallel_pi_target_domain_closed {n : Idx} {t d c : Term}
    (hclosed : ClosedAt n t)
    (h : BetaParallel t (Term.pi d c)) :
    ClosedAt n d := by
  have htarget := betaParallel_preserves_closed hclosed h
  cases htarget with
  | piClosed hdom _ =>
      exact hdom

theorem betaParallel_app_target_left_closed {n : Idx} {t f a : Term}
    (hclosed : ClosedAt n t)
    (h : BetaParallel t (Term.app f a)) :
    ClosedAt n f := by
  have htarget := betaParallel_preserves_closed hclosed h
  cases htarget with
  | appClosed hf _ =>
      exact hf

theorem betaParallel_app_target_right_closed {n : Idx} {t f a : Term}
    (hclosed : ClosedAt n t)
    (h : BetaParallel t (Term.app f a)) :
    ClosedAt n a := by
  have htarget := betaParallel_preserves_closed hclosed h
  cases htarget with
  | appClosed _ ha =>
      exact ha

theorem betaParallel_eq_of_betaNormal {t u : Term}
    (hnormal : BetaNormal t)
    (h : BetaParallel t u) :
    u = t := by
  induction h with
  | var i =>
      rfl
  | sort =>
      rfl
  | app hf ha ihf iha =>
      have hnf := @betaNormal_app_left _ _ hnormal
      have hna := @betaNormal_app_right _ _ hnormal
      have hef := ihf hnf
      have hea := iha hna
      cases hef
      cases hea
      rfl
  | lam hd hb ihd ihb =>
      have hnd := @betaNormal_lam_domain _ _ hnormal
      have hnb := @betaNormal_lam_body _ _ hnormal
      have hed := ihd hnd
      have heb := ihb hnb
      cases hed
      cases heb
      rfl
  | pi hd hc ihd ihc =>
      have hnd := @betaNormal_pi_domain _ _ hnormal
      have hnc := @betaNormal_pi_codomain _ _ hnormal
      have hed := ihd hnd
      have hec := ihc hnc
      cases hed
      cases hec
      rfl
  | beta hd hb ha ihd ihb iha =>
      exact False.elim (hnormal (BetaStep.beta _ _ _))
  | appBeta hf ha ihf iha =>
      have hnf := @betaNormal_app_left _ _ hnormal
      have hef := ihf hnf
      cases hef
      exact False.elim (hnormal (BetaStep.beta _ _ _))

theorem betaParallel_of_normal_source {t u : Term}
    (hnormal : BetaNormal t)
    (h : BetaParallel t u) :
    BetaParallel u t := by
  have heq := betaParallel_eq_of_betaNormal hnormal h
  cases heq
  exact betaParallel_refl t

theorem betaParallel_target_closed_of_normal_source {n : Idx} {t u : Term}
    (hclosed : ClosedAt n t)
    (hnormal : BetaNormal t)
    (h : BetaParallel t u) :
    ClosedAt n u := by
  have heq := betaParallel_eq_of_betaNormal hnormal h
  cases heq
  exact hclosed

theorem betaStarStep_eq_of_betaNormal {t u : Term}
    (hnormal : BetaNormal t)
    (h : BetaStarStep t u) :
    u = t := by
  induction h with
  | refl t =>
      rfl
  | step hstep _ ih =>
      exact False.elim (hnormal hstep)

theorem betaStarStep_of_normal_source {t u : Term}
    (hnormal : BetaNormal t)
    (h : BetaStarStep t u) :
    BetaStarStep u t := by
  have heq := betaStarStep_eq_of_betaNormal hnormal h
  cases heq
  exact BetaStarStep.refl t

theorem betaStarStep_target_closed_of_normal_source {n : Idx} {t u : Term}
    (hclosed : ClosedAt n t)
    (hnormal : BetaNormal t)
    (h : BetaStarStep t u) :
    ClosedAt n u := by
  have heq := betaStarStep_eq_of_betaNormal hnormal h
  cases heq
  exact hclosed

theorem betaParallel_diamond_closed_normal
    {t u v : Term} (_hclosed : ClosedAt 0 t)
    (hnormal : BetaNormal t)
    (h1 : BetaParallel t u) (h2 : BetaParallel t v) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  have hu := betaParallel_eq_of_betaNormal hnormal h1
  have hv := betaParallel_eq_of_betaNormal hnormal h2
  cases hu
  cases hv
  exact
    Exists.intro t
      (And.intro
        (betaParallel_refl t)
        (betaParallel_refl t))

theorem betaStarStep_confluence_closed_normal
    {t u v : Term} (_hclosed : ClosedAt 0 t)
    (hnormal : BetaNormal t)
    (h1 : BetaStarStep t u) (h2 : BetaStarStep t v) :
    ∃ w, BetaStarStep u w ∧ BetaStarStep v w := by
  have hu := betaStarStep_eq_of_betaNormal hnormal h1
  have hv := betaStarStep_eq_of_betaNormal hnormal h2
  cases hu
  cases hv
  exact
    Exists.intro t
      (And.intro
        (BetaStarStep.refl t)
        (BetaStarStep.refl t))

theorem betaParallel_diamond_closed_sort
    {u v : Term}
    (h1 : BetaParallel Term.sort u)
    (h2 : BetaParallel Term.sort v) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  exact betaParallel_diamond_closed_normal ClosedAt.sortClosed betaNormal_sort h1 h2

theorem betaStarStep_confluence_closed_sort
    {u v : Term}
    (h1 : BetaStarStep Term.sort u)
    (h2 : BetaStarStep Term.sort v) :
    ∃ w, BetaStarStep u w ∧ BetaStarStep v w := by
  exact betaStarStep_confluence_closed_normal ClosedAt.sortClosed betaNormal_sort h1 h2

theorem betaNormal_var (i : Idx) :
    BetaNormal (Term.var i) := by
  intro u hstep
  cases hstep

theorem betaParallel_diamond_closed_var_impossible
    {i : Idx} {u v : Term}
    (hclosed : ClosedAt 0 (Term.var i))
    (h1 : BetaParallel (Term.var i) u)
    (h2 : BetaParallel (Term.var i) v) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  exact betaParallel_diamond_closed_normal hclosed (betaNormal_var i) h1 h2

theorem betaStarStep_confluence_closed_var_impossible
    {i : Idx} {u v : Term}
    (hclosed : ClosedAt 0 (Term.var i))
    (h1 : BetaStarStep (Term.var i) u)
    (h2 : BetaStarStep (Term.var i) v) :
    ∃ w, BetaStarStep u w ∧ BetaStarStep v w := by
  exact betaStarStep_confluence_closed_normal hclosed (betaNormal_var i) h1 h2

end BEDC.MetaCIC
