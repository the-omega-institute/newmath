import BEDC.MetaCIC.Normalization.Reducibility
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.TypedExamples.ChurchGallery

namespace BEDC.MetaCIC

namespace PiAdequacy

theorem piCandidate_implies_sn {dom cod f : Term} (h : PiCandidate dom cod f) :
    StrongNormalizable f := by
  exact BEDC.MetaCIC.piCandidate_implies_sn h

end PiAdequacy

inductive NeutralNormal : Term -> Prop
  | var (i : Idx) :
      NeutralNormal (Term.var i)
  | app (f a : Term)
      (hf : NeutralNormal f)
      (ha : StrongNormalizable a) :
      NeutralNormal (Term.app f a)

theorem neutralNormal_step {t t' : Term}
    (h : NeutralNormal t)
    (hbeta : BetaStep t t') :
    NeutralNormal t' := by
  induction h generalizing t' with
  | var i =>
      cases hbeta
  | app f a hf ha ih =>
      cases hbeta with
      | beta dom body arg =>
          cases hf
      | congApp1 f f' a hff' =>
          exact NeutralNormal.app f' a (ih hff') ha
      | congApp2 f a a' haa' =>
          exact NeutralNormal.app f a' hf (strongNormalizable_step ha haa')

theorem neutral_app_sn {f a : Term}
    (hf : NeutralNormal f)
    (hfsn : StrongNormalizable f)
    (ha : StrongNormalizable a) :
    StrongNormalizable (Term.app f a) := by
  revert a hf
  induction hfsn with
  | mk f hnextF ihF =>
      intro a hf ha
      induction ha with
      | mk a hnextA ihA =>
          apply StrongNormalizable.mk
          intro r hbeta
          cases hbeta with
          | beta dom body arg =>
              cases hf
          | congApp1 f f' a hff' =>
              exact ihF f' hff' (neutralNormal_step hf hff')
                (StrongNormalizable.mk a hnextA)
          | congApp2 f a a' haa' =>
              exact ihA a' haa'

theorem neutralNormal_implies_sn {t : Term}
    (h : NeutralNormal t) :
    StrongNormalizable t := by
  induction h with
  | var i =>
      exact var_is_sn i
  | app f a hf ha ih =>
      exact neutral_app_sn hf ih ha

theorem neutralVar_sn (i : Idx) :
    StrongNormalizable (Term.var i) := by
  exact neutralNormal_implies_sn (NeutralNormal.var i)

theorem neutralApp_sn {f a : Term}
    (hf : NeutralNormal f)
    (ha : StrongNormalizable a) :
    StrongNormalizable (Term.app f a) := by
  exact neutral_app_sn hf (neutralNormal_implies_sn hf) ha

theorem sn_lam {d b : Term}
    (hd : StrongNormalizable d)
    (hb : StrongNormalizable b) :
    StrongNormalizable (Term.lam d b) := by
  revert b
  induction hd with
  | mk d hnextD ihD =>
      intro b hb
      induction hb with
      | mk b hnextB ihB =>
          apply StrongNormalizable.mk
          intro r hbeta
          cases hbeta with
          | congLam d b b' hbb' =>
              exact ihB b' hbb'
          | congLamDom d d' b hdd' =>
              exact ihD d' hdd' (StrongNormalizable.mk b hnextB)

theorem sn_pi {d c : Term}
    (hd : StrongNormalizable d)
    (hc : StrongNormalizable c) :
    StrongNormalizable (Term.pi d c) := by
  revert c
  induction hd with
  | mk d hnextD ihD =>
      intro c hc
      induction hc with
      | mk c hnextC ihC =>
          apply StrongNormalizable.mk
          intro r hbeta
          cases hbeta with
          | congPiCod d c c' hcc' =>
              exact ihC c' hcc'
          | congPiDom d d' c hdd' =>
              exact ihD d' hdd' (StrongNormalizable.mk c hnextC)

theorem neutral_var_zero_sn :
    StrongNormalizable (Term.var 0) := by
  exact neutralVar_sn 0

theorem neutral_var_one_sn :
    StrongNormalizable (Term.var 1) := by
  exact neutralVar_sn 1

theorem neutral_var_two_sn :
    StrongNormalizable (Term.var 2) := by
  exact neutralVar_sn 2

theorem neutral_var_three_sn :
    StrongNormalizable (Term.var 3) := by
  exact neutralVar_sn 3

theorem var_zero_to_one_pi_sn :
    StrongNormalizable (Term.pi (Term.var 0) (Term.var 1)) := by
  exact sn_pi neutral_var_zero_sn neutral_var_one_sn

theorem churchBoolTy_sn :
    StrongNormalizable churchBoolTy := by
  exact sn_pi sort_is_sn
    (sn_pi neutral_var_zero_sn
      (sn_pi neutral_var_one_sn neutral_var_two_sn))

theorem polyIdentity_sn :
    StrongNormalizable (Term.lam Term.sort (Term.lam (Term.var 0) (Term.var 0))) := by
  exact sn_lam sort_is_sn
    (sn_lam neutral_var_zero_sn neutral_var_zero_sn)

theorem churchIdentityTm_sn :
    StrongNormalizable churchIdentityTm := by
  exact polyIdentity_sn

theorem churchIdentityTy_sn :
    StrongNormalizable churchIdentityTy := by
  exact sn_pi sort_is_sn
    (sn_pi neutral_var_zero_sn neutral_var_one_sn)

theorem churchTrueTm_sn :
    StrongNormalizable churchTrueTm := by
  exact sn_lam sort_is_sn
    (sn_lam neutral_var_zero_sn
      (sn_lam neutral_var_one_sn neutral_var_one_sn))

theorem church_true_sn :
    StrongNormalizable churchTrueTm := by
  exact churchTrueTm_sn

theorem churchFalseTm_sn :
    StrongNormalizable churchFalseTm := by
  exact sn_lam sort_is_sn
    (sn_lam neutral_var_zero_sn
      (sn_lam neutral_var_one_sn neutral_var_zero_sn))

theorem church_false_sn :
    StrongNormalizable churchFalseTm := by
  exact churchFalseTm_sn

theorem churchNatTy_sn :
    StrongNormalizable churchNatTy := by
  exact sn_pi sort_is_sn
    (sn_pi var_zero_to_one_pi_sn
      (sn_pi neutral_var_one_sn neutral_var_two_sn))

theorem churchZeroTm_sn :
    StrongNormalizable churchZeroTm := by
  exact sn_lam sort_is_sn
    (sn_lam var_zero_to_one_pi_sn
      (sn_lam neutral_var_one_sn neutral_var_zero_sn))

theorem church_zero_sn :
    StrongNormalizable churchZeroTm := by
  exact churchZeroTm_sn

theorem churchOneTm_inner_neutral_sn :
    StrongNormalizable (Term.app (Term.var 1) (Term.var 0)) := by
  exact neutralApp_sn (NeutralNormal.var 1) neutral_var_zero_sn

theorem churchOneTm_sn :
    StrongNormalizable churchOneTm := by
  exact sn_lam sort_is_sn
    (sn_lam var_zero_to_one_pi_sn
      (sn_lam neutral_var_one_sn churchOneTm_inner_neutral_sn))

theorem churchConstTy_sn :
    StrongNormalizable churchConstTy := by
  exact sn_pi sort_is_sn
    (sn_pi sort_is_sn
      (sn_pi neutral_var_one_sn
        (sn_pi neutral_var_one_sn neutral_var_three_sn)))

theorem churchConstTm_sn :
    StrongNormalizable churchConstTm := by
  exact sn_lam sort_is_sn
    (sn_lam sort_is_sn
      (sn_lam neutral_var_one_sn
        (sn_lam neutral_var_one_sn neutral_var_one_sn)))

theorem churchSuccTy_sn :
    StrongNormalizable churchSuccTy := by
  exact sn_pi churchNatTy_sn churchNatTy_sn

theorem churchSuccTm_spine_sn :
    StrongNormalizable
      (Term.app (Term.var 1)
        (Term.app
          (Term.app
            (Term.app (Term.var 3) (Term.var 2))
            (Term.var 1))
          (Term.var 0))) := by
  have h1 :
      StrongNormalizable (Term.app (Term.var 3) (Term.var 2)) := by
    exact neutralApp_sn (NeutralNormal.var 3) neutral_var_two_sn
  have h2 :
      StrongNormalizable
        (Term.app
          (Term.app (Term.var 3) (Term.var 2))
          (Term.var 1)) := by
    exact neutralApp_sn
      (NeutralNormal.app (Term.var 3) (Term.var 2)
        (NeutralNormal.var 3) neutral_var_two_sn)
      neutral_var_one_sn
  have h3 :
      StrongNormalizable
        (Term.app
          (Term.app
            (Term.app (Term.var 3) (Term.var 2))
            (Term.var 1))
          (Term.var 0)) := by
    exact neutralApp_sn
      (NeutralNormal.app
        (Term.app (Term.var 3) (Term.var 2))
        (Term.var 1)
        (NeutralNormal.app (Term.var 3) (Term.var 2)
          (NeutralNormal.var 3) neutral_var_two_sn)
        neutral_var_one_sn)
      neutral_var_zero_sn
  exact neutralApp_sn (NeutralNormal.var 1) h3

theorem churchSuccTm_sn :
    StrongNormalizable churchSuccTm := by
  exact sn_lam churchNatTy_sn
    (sn_lam sort_is_sn
      (sn_lam var_zero_to_one_pi_sn
        (sn_lam neutral_var_one_sn churchSuccTm_spine_sn)))

end BEDC.MetaCIC
