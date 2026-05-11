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

theorem betaStep_to_parallel {t u : Term} :
    BetaStep t u → BetaParallel t u := by
  intro h
  induction h with
  | beta dom body arg =>
      exact
        BetaParallel.beta
          (betaParallel_refl dom)
          (betaParallel_refl body)
          (betaParallel_refl arg)
  | congApp1 f f' a hff' ih =>
      exact BetaParallel.app ih (betaParallel_refl a)
  | congApp2 f a a' haa' ih =>
      exact BetaParallel.app (betaParallel_refl f) ih
  | congLam d b b' hbb' ih =>
      exact BetaParallel.lam (betaParallel_refl d) ih

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
      cases hg with
      | intro hf1g hf2g =>
          cases ha with
          | intro b hb =>
              cases hb with
              | intro ha1b ha2b =>
                  exact
                    Exists.intro
                      (Term.app g b)
                      (And.intro
                        (BetaParallel.app hf1g ha1b)
                        (BetaParallel.app hf2g ha2b))

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
      cases he with
      | intro hd1e hd2e =>
          cases hb with
          | intro c hc =>
              cases hc with
              | intro hb1c hb2c =>
                  exact
                    Exists.intro
                      (Term.lam e c)
                      (And.intro
                        (BetaParallel.lam hd1e hb1c)
                        (BetaParallel.lam hd2e hb2c))

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
      cases he with
      | intro hd1e hd2e =>
          cases hc with
          | intro r hr =>
              cases hr with
              | intro hc1r hc2r =>
                  exact
                    Exists.intro
                      (Term.pi e r)
                      (And.intro
                        (BetaParallel.pi hd1e hc1r)
                        (BetaParallel.pi hd2e hc2r))

end BEDC.MetaCIC
