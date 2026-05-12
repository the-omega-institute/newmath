import BEDC.MetaCIC.Beta

namespace BEDC.MetaCIC

inductive BetaStarStep : Term → Term → Prop
  | refl (t : Term) :
      BetaStarStep t t
  | step {t u v : Term} :
      BetaStep t u →
      BetaStarStep u v →
      BetaStarStep t v

def BetaStarConfluent : Prop :=
  ∀ {t u1 u2 : Term},
    BetaStarStep t u1 →
    BetaStarStep t u2 →
    Exists (fun v => BetaStarStep u1 v ∧ BetaStarStep u2 v)

inductive BetaParallel : Term → Term → Prop
  | var (i : Idx) :
      BetaParallel (Term.var i) (Term.var i)
  | sort :
      BetaParallel Term.sort Term.sort
  | app {f f' a a' : Term} :
      BetaParallel f f' →
      BetaParallel a a' →
      BetaParallel (Term.app f a) (Term.app f' a')
  | lam {d d' b b' : Term} :
      BetaParallel d d' →
      BetaParallel b b' →
      BetaParallel (Term.lam d b) (Term.lam d' b')
  | pi {d d' c c' : Term} :
      BetaParallel d d' →
      BetaParallel c c' →
      BetaParallel (Term.pi d c) (Term.pi d' c')
  | beta {d d' b b' a a' : Term} :
      BetaParallel d d' →
      BetaParallel b b' →
      BetaParallel a a' →
      BetaParallel (Term.app (Term.lam d b) a) (substitute 0 a' b')

def BetaParallelDiamond : Prop :=
  ∀ {t u1 u2 : Term},
    BetaParallel t u1 →
    BetaParallel t u2 →
    Exists (fun v => BetaParallel u1 v ∧ BetaParallel u2 v)

theorem betaStarStep_refl_self (t : Term) :
    BetaStarStep t t := by
  exact BetaStarStep.refl t

theorem betaStar_one {t u : Term} :
    BetaStep t u → BetaStarStep t u := by
  intro h
  exact BetaStarStep.step h (BetaStarStep.refl u)

theorem betaStar_trans {t u v : Term} :
    BetaStarStep t u → BetaStarStep u v → BetaStarStep t v := by
  intro htu huv
  induction htu with
  | refl t =>
      exact huv
  | step htw hwu ih =>
      exact BetaStarStep.step htw (ih huv)

theorem betaStarStep_concat {t t' t'' : Term}
    (h1 : BetaStarStep t t') (h2 : BetaStep t' t'') :
    BetaStarStep t t'' := by
  exact betaStar_trans h1 (betaStar_one h2)

theorem betaStarStep_cons {t t' t'' : Term}
    (h1 : BetaStep t t') (h2 : BetaStarStep t' t'') :
    BetaStarStep t t'' := by
  exact BetaStarStep.step h1 h2

theorem betaStarStep_of_two_steps {t t' t'' : Term}
    (h1 : BetaStep t t') (h2 : BetaStep t' t'') :
    BetaStarStep t t'' := by
  exact BetaStarStep.step h1 (BetaStarStep.step h2 (BetaStarStep.refl t''))

theorem betaStarStep_triple {a b c d : Term}
    (h1 : BetaStarStep a b) (h2 : BetaStarStep b c) (h3 : BetaStarStep c d) :
    BetaStarStep a d := by
  exact betaStar_trans h1 (betaStar_trans h2 h3)

theorem betaStarStep_three_steps {a b c d : Term}
    (h1 : BetaStep a b) (h2 : BetaStep b c) (h3 : BetaStep c d) :
    BetaStarStep a d := by
  exact betaStar_trans (betaStarStep_of_two_steps h1 h2) (betaStar_one h3)

theorem betaStarStep_lam_cong {d b b' : Term} :
    BetaStarStep b b' → BetaStarStep (Term.lam d b) (Term.lam d b') := by
  intro h
  induction h with
  | refl t =>
      exact BetaStarStep.refl (Term.lam d t)
  | step htw hwu ih =>
      exact BetaStarStep.step (BetaStep.congLam d _ _ htw) ih

theorem betaStarStep_app_left {f f' a : Term} :
    BetaStarStep f f' → BetaStarStep (Term.app f a) (Term.app f' a) := by
  intro h
  induction h with
  | refl t =>
      exact BetaStarStep.refl (Term.app t a)
  | step htw hwu ih =>
      exact BetaStarStep.step (BetaStep.congApp1 _ _ a htw) ih

theorem betaStarStep_app_right {f a a' : Term} :
    BetaStarStep a a' → BetaStarStep (Term.app f a) (Term.app f a') := by
  intro h
  induction h with
  | refl t =>
      exact BetaStarStep.refl (Term.app f t)
  | step htw hwu ih =>
      exact BetaStarStep.step (BetaStep.congApp2 f _ _ htw) ih

theorem betaStarStep_app_double {f f' a a' : Term}
    (hf : BetaStarStep f f') (ha : BetaStarStep a a') :
    BetaStarStep (Term.app f a) (Term.app f' a') := by
  exact betaStar_trans (betaStarStep_app_left hf) (betaStarStep_app_right ha)

theorem betaStarStep_pi_cod (d : Term) {c c' : Term}
    (h : BetaStarStep c c') :
    BetaStarStep (Term.pi d c) (Term.pi d c') := by
  induction h with
  | refl t =>
      exact BetaStarStep.refl (Term.pi d t)
  | step htw hwu ih =>
      exact BetaStarStep.step (BetaStep.congPiCod d _ _ htw) ih

theorem betaStarStep_pi_dom {d d' : Term} (c : Term)
    (h : BetaStarStep d d') :
    BetaStarStep (Term.pi d c) (Term.pi d' c) := by
  induction h with
  | refl t =>
      exact BetaStarStep.refl (Term.pi t c)
  | step htw hwu ih =>
      exact BetaStarStep.step (BetaStep.congPiDom _ _ c htw) ih

theorem betaStarStep_pi_double {d d' c c' : Term}
    (hd : BetaStarStep d d') (hc : BetaStarStep c c') :
    BetaStarStep (Term.pi d c) (Term.pi d' c') := by
  exact betaStar_trans (betaStarStep_pi_dom c hd) (betaStarStep_pi_cod d' hc)

theorem betaStarStep_lam_dom {d d' : Term} (b : Term)
    (h : BetaStarStep d d') :
    BetaStarStep (Term.lam d b) (Term.lam d' b) := by
  induction h with
  | refl t =>
      exact BetaStarStep.refl (Term.lam t b)
  | step htw hwu ih =>
      exact BetaStarStep.step (BetaStep.congLamDom _ _ b htw) ih

theorem betaStarStep_lam_double {d d' b b' : Term}
    (hd : BetaStarStep d d') (hb : BetaStarStep b b') :
    BetaStarStep (Term.lam d b) (Term.lam d' b') := by
  exact betaStar_trans (betaStarStep_lam_dom b hd) (betaStarStep_lam_cong hb)

theorem betaParallel_refl (t : Term) :
    BetaParallel t t := by
  induction t with
  | var i =>
      exact BetaParallel.var i
  | app f a hf ha =>
      exact BetaParallel.app hf ha
  | lam d b hd hb =>
      exact BetaParallel.lam hd hb
  | pi d c hd hc =>
      exact BetaParallel.pi hd hc
  | sort =>
      exact BetaParallel.sort

theorem betaParallel_app_cong {f f' a a' : Term}
    (hf : BetaParallel f f') (ha : BetaParallel a a') :
    BetaParallel (Term.app f a) (Term.app f' a') := by
  exact BetaParallel.app hf ha

theorem betaParallel_pi_cong {d d' c c' : Term}
    (hd : BetaParallel d d') (hc : BetaParallel c c') :
    BetaParallel (Term.pi d c) (Term.pi d' c') := by
  exact BetaParallel.pi hd hc

theorem betaParallel_lam_cong {d d' b b' : Term}
    (hd : BetaParallel d d') (hb : BetaParallel b b') :
    BetaParallel (Term.lam d b) (Term.lam d' b') := by
  exact BetaParallel.lam hd hb

theorem betaStep_to_parallel {t u : Term} :
    BetaStep t u → BetaParallel t u := by
  intro h
  induction h with
  | beta dom body arg =>
      exact BetaParallel.beta (betaParallel_refl dom) (betaParallel_refl body)
        (betaParallel_refl arg)
  | congApp1 f f' a hff' ih =>
      exact BetaParallel.app ih (betaParallel_refl a)
  | congApp2 f a a' haa' ih =>
      exact BetaParallel.app (betaParallel_refl f) ih
  | congLam d b b' hbb' ih =>
      exact BetaParallel.lam (betaParallel_refl d) ih
  | congPiCod d c c' hcc' ih =>
      exact BetaParallel.pi (betaParallel_refl d) ih
  | congPiDom d d' c hdd' ih =>
      exact BetaParallel.pi ih (betaParallel_refl c)
  | congLamDom d d' b hdd' ih =>
      exact BetaParallel.lam ih (betaParallel_refl b)

theorem betaStep_to_betaParallel {t t' : Term}
    (h : BetaStep t t') :
    BetaParallel t t' := by
  exact betaStep_to_parallel h

theorem betaParallel_of_betaStep {t t' : Term}
    (h : BetaStep t t') :
    BetaParallel t t' := by
  exact betaStep_to_parallel h

theorem betaParallel_app_cong_step {f f' a : Term}
    (h : BetaStep f f') :
    BetaParallel (Term.app f a) (Term.app f' a) := by
  exact BetaParallel.app (betaParallel_of_betaStep h) (betaParallel_refl a)

theorem betaParallel_to_betaStar {t u : Term} :
    BetaParallel t u → BetaStarStep t u := by
  intro h
  induction h with
  | var i =>
      exact BetaStarStep.refl (Term.var i)
  | sort =>
      exact BetaStarStep.refl Term.sort
  | app hf ha ihf iha =>
      exact betaStar_trans (betaStarStep_app_left ihf) (betaStarStep_app_right iha)
  | lam hd hb ihd ihb =>
      exact betaStar_trans (betaStarStep_lam_dom _ ihd) (betaStarStep_lam_cong ihb)
  | pi hd hc ihd ihc =>
      exact betaStar_trans (betaStarStep_pi_dom _ ihd) (betaStarStep_pi_cod _ ihc)
  | beta hd hb ha ihd ihb iha =>
      exact
        betaStar_trans
          (betaStarStep_app_left (betaStarStep_lam_dom _ ihd))
          (betaStar_trans
            (betaStarStep_app_left (betaStarStep_lam_cong ihb))
            (betaStar_trans
              (betaStarStep_app_right iha)
              (betaStar_one (BetaStep.beta _ _ _))))

theorem betaParallel_sort_unique {t : Term}
    (h : BetaParallel Term.sort t) :
    t = Term.sort := by
  cases h
  rfl

theorem betaParallel_sort_unique_target {t : Term}
    (h : BetaParallel Term.sort t) :
    t = Term.sort := by
  cases h
  rfl

theorem betaStarStep_of_betaParallel_sort {t : Term}
    (h : BetaParallel Term.sort t) :
    BetaStarStep Term.sort t := by
  cases betaParallel_sort_unique h
  exact BetaStarStep.refl Term.sort

theorem betaParallel_var_unique {i : Idx} {t : Term}
    (h : BetaParallel (Term.var i) t) :
    t = Term.var i := by
  cases h
  rfl

theorem betaParallel_var_unique_target {i : Idx} {t : Term}
    (h : BetaParallel (Term.var i) t) :
    t = Term.var i := by
  cases h
  rfl

theorem betaStarStep_of_betaParallel_var {i : Idx} {t : Term}
    (h : BetaParallel (Term.var i) t) :
    BetaStarStep (Term.var i) t := by
  cases betaParallel_var_unique h
  exact BetaStarStep.refl (Term.var i)

theorem betaParallel_pi_shape {d c t : Term}
    (h : BetaParallel (Term.pi d c) t) :
    ∃ d' c', t = Term.pi d' c' ∧ BetaParallel d d' ∧ BetaParallel c c' := by
  cases h with
  | pi hd hc =>
      exact Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro hd hc)))

theorem betaParallel_lam_shape {d b t : Term}
    (h : BetaParallel (Term.lam d b) t) :
    ∃ d' b', t = Term.lam d' b' ∧ BetaParallel d d' ∧ BetaParallel b b' := by
  cases h with
  | lam hd hb =>
      exact Exists.intro _ (Exists.intro _ (And.intro rfl (And.intro hd hb)))

theorem betaParallel_app_shape {f a t : Term}
    (h : BetaParallel (Term.app f a) t) :
    (∃ f' a', BetaParallel f f' ∧ BetaParallel a a' ∧ t = Term.app f' a') ∨
    (∃ d body body' a',
      BetaParallel body body' ∧ BetaParallel a a' ∧
        f = Term.lam d body ∧ t = substitute 0 a' body') := by
  cases h with
  | app hf ha =>
      exact Or.inl ⟨_, _, hf, ha, rfl⟩
  | beta hd hb ha =>
      exact Or.inr ⟨_, _, _, _, hb, ha, rfl, rfl⟩

theorem betaStarStep_of_betaParallel_atom {t t' : Term}
    (hatom : t = Term.sort ∨ ∃ i, t = Term.var i)
    (h : BetaParallel t t') :
    BetaStarStep t t' := by
  cases hatom with
  | inl hsort =>
      cases hsort
      cases betaParallel_sort_unique h
      exact BetaStarStep.refl Term.sort
  | inr hvar =>
      cases hvar with
      | intro i hi =>
          cases hi
          cases betaParallel_var_unique h
          exact BetaStarStep.refl (Term.var i)

theorem betaParallel_join_refl_left {t u : Term} :
    BetaParallel t u →
    Exists (fun v => BetaParallel t v ∧ BetaParallel u v) := by
  intro h
  exact Exists.intro u (And.intro h (betaParallel_refl u))

theorem betaParallel_join_refl_right {t u : Term} :
    BetaParallel t u →
    Exists (fun v => BetaParallel u v ∧ BetaParallel t v) := by
  intro h
  exact Exists.intro u (And.intro (betaParallel_refl u) h)

theorem betaParallel_var_diamond
    (i : Idx) {u1 u2 : Term}
    (h1 : BetaParallel (Term.var i) u1)
    (h2 : BetaParallel (Term.var i) u2) :
    Exists (fun v => BetaParallel u1 v ∧ BetaParallel u2 v) := by
  cases h1
  cases h2
  exact ⟨Term.var i, BetaParallel.var i, BetaParallel.var i⟩

theorem betaParallel_diamond_var {i : Idx} {t1 t2 : Term}
    (h1 : BetaParallel (Term.var i) t1) (h2 : BetaParallel (Term.var i) t2) :
    ∃ v, BetaParallel t1 v ∧ BetaParallel t2 v := by
  cases betaParallel_var_unique h1
  cases betaParallel_var_unique h2
  exact
    Exists.intro
      (Term.var i)
      (And.intro (BetaParallel.var i) (BetaParallel.var i))

theorem betaParallel_sort_diamond
    {u1 u2 : Term}
    (h1 : BetaParallel Term.sort u1)
    (h2 : BetaParallel Term.sort u2) :
    Exists (fun v => BetaParallel u1 v ∧ BetaParallel u2 v) := by
  cases h1
  cases h2
  exact ⟨Term.sort, BetaParallel.sort, BetaParallel.sort⟩

theorem betaParallel_diamond_sort {t1 t2 : Term}
    (h1 : BetaParallel Term.sort t1) (h2 : BetaParallel Term.sort t2) :
    ∃ v, BetaParallel t1 v ∧ BetaParallel t2 v := by
  cases betaParallel_sort_unique h1
  cases betaParallel_sort_unique h2
  exact
    Exists.intro
      Term.sort
      (And.intro BetaParallel.sort BetaParallel.sort)

theorem betaParallel_app_diamond_of_components
    {f1 f2 a1 a2 : Term}
    (hf :
      Exists (fun g => BetaParallel f1 g ∧ BetaParallel f2 g))
    (ha :
      Exists (fun b => BetaParallel a1 b ∧ BetaParallel a2 b)) :
    Exists
      (fun v =>
        BetaParallel (Term.app f1 a1) v ∧
          BetaParallel (Term.app f2 a2) v) := by
  cases hf with
  | intro g hg =>
      cases ha with
      | intro b hb =>
          exact ⟨Term.app g b, BetaParallel.app hg.left hb.left,
            BetaParallel.app hg.right hb.right⟩

theorem betaParallel_lam_diamond_of_components
    {d1 d2 b1 b2 : Term}
    (hd :
      Exists (fun e => BetaParallel d1 e ∧ BetaParallel d2 e))
    (hb :
      Exists (fun c => BetaParallel b1 c ∧ BetaParallel b2 c)) :
    Exists
      (fun v =>
        BetaParallel (Term.lam d1 b1) v ∧
          BetaParallel (Term.lam d2 b2) v) := by
  cases hd with
  | intro e he =>
      cases hb with
      | intro c hc =>
          exact ⟨Term.lam e c, BetaParallel.lam he.left hc.left,
            BetaParallel.lam he.right hc.right⟩

theorem betaParallel_pi_diamond_of_components
    {d1 d2 c1 c2 : Term}
    (hd :
      Exists (fun e => BetaParallel d1 e ∧ BetaParallel d2 e))
    (hc :
      Exists (fun r => BetaParallel c1 r ∧ BetaParallel c2 r)) :
    Exists
      (fun v =>
        BetaParallel (Term.pi d1 c1) v ∧
          BetaParallel (Term.pi d2 c2) v) := by
  cases hd with
  | intro e he =>
      cases hc with
      | intro r hr =>
          exact ⟨Term.pi e r, BetaParallel.pi he.left hr.left,
            BetaParallel.pi he.right hr.right⟩

theorem betaParallel_app_independent_diamond
    {f a f1 f2 a1 a2 : Term}
    (hf1 : BetaParallel f f1)
    (hf2 : BetaParallel f f2)
    (ha1 : BetaParallel a a1)
    (ha2 : BetaParallel a a2)
    (hf :
      ∀ {g1 g2 : Term},
        BetaParallel f g1 →
        BetaParallel f g2 →
        Exists (fun g => BetaParallel g1 g ∧ BetaParallel g2 g))
    (ha :
      ∀ {b1 b2 : Term},
        BetaParallel a b1 →
        BetaParallel a b2 →
        Exists (fun b => BetaParallel b1 b ∧ BetaParallel b2 b)) :
    Exists
      (fun v =>
        BetaParallel (Term.app f1 a1) v ∧
          BetaParallel (Term.app f2 a2) v) := by
  exact
    betaParallel_app_diamond_of_components
      (hf hf1 hf2)
      (ha ha1 ha2)

theorem betaParallel_lam_shape_diamond
    {d b u1 u2 : Term}
    (h1 : BetaParallel (Term.lam d b) u1)
    (h2 : BetaParallel (Term.lam d b) u2)
    (hd :
      ∀ {d1 d2 : Term},
        BetaParallel d d1 →
        BetaParallel d d2 →
        Exists (fun e => BetaParallel d1 e ∧ BetaParallel d2 e))
    (hb :
      ∀ {b1 b2 : Term},
        BetaParallel b b1 →
        BetaParallel b b2 →
        Exists (fun c => BetaParallel b1 c ∧ BetaParallel b2 c)) :
    Exists (fun v => BetaParallel u1 v ∧ BetaParallel u2 v) := by
  cases h1 with
  | lam hd1 hb1 =>
      cases h2 with
      | lam hd2 hb2 =>
          exact
            betaParallel_lam_diamond_of_components
              (hd hd1 hd2)
              (hb hb1 hb2)

theorem betaParallel_pi_shape_diamond
    {d c u1 u2 : Term}
    (h1 : BetaParallel (Term.pi d c) u1)
    (h2 : BetaParallel (Term.pi d c) u2)
    (hd :
      ∀ {d1 d2 : Term},
        BetaParallel d d1 →
        BetaParallel d d2 →
        Exists (fun e => BetaParallel d1 e ∧ BetaParallel d2 e))
    (hc :
      ∀ {c1 c2 : Term},
        BetaParallel c c1 →
        BetaParallel c c2 →
        Exists (fun r => BetaParallel c1 r ∧ BetaParallel c2 r)) :
    Exists (fun v => BetaParallel u1 v ∧ BetaParallel u2 v) := by
  cases h1 with
  | pi hd1 hc1 =>
      cases h2 with
      | pi hd2 hc2 =>
          exact
            betaParallel_pi_diamond_of_components
              (hd hd1 hd2)
              (hc hc1 hc2)

end BEDC.MetaCIC
