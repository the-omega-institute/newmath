import BEDC.MetaCIC.Confluence.AtomJoin
import BEDC.MetaCIC.Substitution.Core

namespace BEDC.MetaCIC

def BetaParallelSubstitutionCompatibility : Prop :=
  ∀ {a a' b b' : Term},
    BetaParallel a a' →
    BetaParallel b b' →
    BetaParallel (substitute 0 a b) (substitute 0 a' b')

theorem substitute_commutation_unclosed_obstruction :
    substitute 0 (Term.var 0)
        (substitute 0 Term.sort (Term.var 1)) ≠
      substitute 0 (substitute 0 (Term.var 0) Term.sort)
        (substitute 1 (Term.var 0) (Term.var 1)) := by
  exact substitute_substitute_zero_zero_unclosed_counterexample

theorem betaParallel_pi_shape_full_diamond
    {d c d' c' d'' c'' : Term}
    (h1 : BetaParallel (Term.pi d c) (Term.pi d' c'))
    (h2 : BetaParallel (Term.pi d c) (Term.pi d'' c''))
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
    ∃ d''' c''',
      BetaParallel (Term.pi d' c') (Term.pi d''' c''') ∧
        BetaParallel (Term.pi d'' c'') (Term.pi d''' c''') := by
  cases h1 with
  | pi hd1 hc1 =>
      cases h2 with
      | pi hd2 hc2 =>
          cases hd hd1 hd2 with
          | intro d''' hdjoin =>
              cases hdjoin with
              | intro hdleft hdright =>
                  cases hc hc1 hc2 with
                  | intro c''' hcjoin =>
                      cases hcjoin with
                      | intro hcleft hcright =>
                          exact
                            Exists.intro d'''
                              (Exists.intro c'''
                                (And.intro
                                  (BetaParallel.pi hdleft hcleft)
                                  (BetaParallel.pi hdright hcright)))

theorem betaParallel_lam_shape_full_diamond
    {d b d' b' d'' b'' : Term}
    (h1 : BetaParallel (Term.lam d b) (Term.lam d' b'))
    (h2 : BetaParallel (Term.lam d b) (Term.lam d'' b''))
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
    ∃ d''' b''',
      BetaParallel (Term.lam d' b') (Term.lam d''' b''') ∧
        BetaParallel (Term.lam d'' b'') (Term.lam d''' b''') := by
  cases h1 with
  | lam hd1 hb1 =>
      cases h2 with
      | lam hd2 hb2 =>
          cases hd hd1 hd2 with
          | intro d''' hdjoin =>
              cases hdjoin with
              | intro hdleft hdright =>
                  cases hb hb1 hb2 with
                  | intro b''' hbjoin =>
                      cases hbjoin with
                      | intro hbleft hbright =>
                          exact
                            Exists.intro d'''
                              (Exists.intro b'''
                                (And.intro
                                  (BetaParallel.lam hdleft hbleft)
                                  (BetaParallel.lam hdright hbright)))

theorem betaParallel_app_cong_cong_diamond
    {f a f' a' f'' a'' : Term}
    (hf1 : BetaParallel f f')
    (hf2 : BetaParallel f f'')
    (ha1 : BetaParallel a a')
    (ha2 : BetaParallel a a'')
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
      (fun w =>
        BetaParallel (Term.app f' a') w ∧
          BetaParallel (Term.app f'' a'') w) := by
  exact
    betaParallel_app_diamond_of_components
      (hf hf1 hf2)
      (ha ha1 ha2)

theorem betaParallel_app_shape_diamond_from_substitution
    (hsubst : BetaParallelSubstitutionCompatibility)
    {f a u v : Term}
    (h1 : BetaParallel (Term.app f a) u)
    (h2 : BetaParallel (Term.app f a) v)
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
    Exists (fun w => BetaParallel u w ∧ BetaParallel v w) := by
  have hshape1 := betaParallel_app_shape h1
  have hshape2 := betaParallel_app_shape h2
  cases hshape1 with
  | inl hcong1 =>
      cases hcong1 with
      | intro f1 hf1pack =>
          cases hf1pack with
          | intro a1 hpack1 =>
              cases hpack1 with
              | intro hf1 hrest1 =>
                  cases hrest1 with
                  | intro ha1 hu =>
                      cases hshape2 with
                      | inl hcong2 =>
                          cases hcong2 with
                          | intro f2 hf2pack =>
                              cases hf2pack with
                              | intro a2 hpack2 =>
                                  cases hpack2 with
                                  | intro hf2 hrest2 =>
                                      cases hrest2 with
                                      | intro ha2 hv =>
                                          cases hu
                                          cases hv
                                          exact
                                            betaParallel_app_cong_cong_diamond
                                              hf1 hf2 ha1 ha2 hf ha
                      | inr hbeta2 =>
                          cases hbeta2 with
                          | intro d2 hd2pack =>
                              cases hd2pack with
                              | intro b2 hb2pack =>
                                  cases hb2pack with
                                  | intro a2 hpack2 =>
                                      cases hpack2 with
                                      | intro hf2 hrest2 =>
                                          cases hrest2 with
                                          | intro ha2 hv =>
                                              cases hu
                                              cases hv
                                              cases hf hf1 hf2 with
                                              | intro g hg =>
                                                  cases hg with
                                                  | intro hf1g hlamg =>
                                                      have hlamInv :=
                                                        betaParallel_lam_inv hlamg
                                                      cases hlamInv with
                                                      | intro d3 hd3pack =>
                                                          cases hd3pack with
                                                          | intro b3 hpack3 =>
                                                              cases hpack3 with
                                                              | intro hgEq hrest3 =>
                                                                  cases hrest3 with
                                                                  | intro _ hb23 =>
                                                                      cases hgEq
                                                                      cases ha ha1 ha2 with
                                                                      | intro a3 hajoin =>
                                                                          cases hajoin with
                                                                          | intro ha13 ha23 =>
                                                                              exact
                                                                                Exists.intro
                                                                                  (substitute 0 a3 b3)
                                                                                  (And.intro
                                                                                    (BetaParallel.appBeta hf1g ha13)
                                                                                    (hsubst ha23 hb23))
  | inr hbeta1 =>
      cases hbeta1 with
      | intro d1 hd1pack =>
          cases hd1pack with
          | intro b1 hb1pack =>
              cases hb1pack with
              | intro a1 hpack1 =>
                  cases hpack1 with
                  | intro hf1 hrest1 =>
                      cases hrest1 with
                      | intro ha1 hu =>
                          cases hshape2 with
                          | inl hcong2 =>
                              cases hcong2 with
                              | intro f2 hf2pack =>
                                  cases hf2pack with
                                  | intro a2 hpack2 =>
                                      cases hpack2 with
                                      | intro hf2 hrest2 =>
                                          cases hrest2 with
                                          | intro ha2 hv =>
                                              cases hu
                                              cases hv
                                              cases hf hf1 hf2 with
                                              | intro g hg =>
                                                  cases hg with
                                                  | intro hlamg hf2g =>
                                                      have hlamInv :=
                                                        betaParallel_lam_inv hlamg
                                                      cases hlamInv with
                                                      | intro d3 hd3pack =>
                                                          cases hd3pack with
                                                          | intro b3 hpack3 =>
                                                              cases hpack3 with
                                                              | intro hgEq hrest3 =>
                                                                  cases hrest3 with
                                                                  | intro _ hb13 =>
                                                                      cases hgEq
                                                                      cases ha ha1 ha2 with
                                                                      | intro a3 hajoin =>
                                                                          cases hajoin with
                                                                          | intro ha13 ha23 =>
                                                                              exact
                                                                                Exists.intro
                                                                                  (substitute 0 a3 b3)
                                                                                  (And.intro
                                                                                    (hsubst ha13 hb13)
                                                                                    (BetaParallel.appBeta hf2g ha23))
                          | inr hbeta2 =>
                              cases hbeta2 with
                              | intro d2 hd2pack =>
                                  cases hd2pack with
                                  | intro b2 hb2pack =>
                                      cases hb2pack with
                                      | intro a2 hpack2 =>
                                          cases hpack2 with
                                          | intro hf2 hrest2 =>
                                              cases hrest2 with
                                              | intro ha2 hv =>
                                                  cases hu
                                                  cases hv
                                                  cases hf hf1 hf2 with
                                                  | intro g hg =>
                                                      cases hg with
                                                      | intro hlam1g hlam2g =>
                                                          have hlamInv1 :=
                                                            betaParallel_lam_inv hlam1g
                                                          cases hlamInv1 with
                                                          | intro d3 hd3pack =>
                                                              cases hd3pack with
                                                              | intro b3 hpack3 =>
                                                                  cases hpack3 with
                                                                  | intro hgEq hrest3 =>
                                                                      cases hrest3 with
                                                                      | intro _ hb13 =>
                                                                          cases hgEq
                                                                          have hlamInv2 :=
                                                                            betaParallel_lam_inv hlam2g
                                                                          cases hlamInv2 with
                                                                          | intro d4 hd4pack =>
                                                                              cases hd4pack with
                                                                              | intro b4 hpack4 =>
                                                                                  cases hpack4 with
                                                                                  | intro htargetEq hrest4 =>
                                                                                      cases htargetEq
                                                                                      cases hrest4 with
                                                                                      | intro _ hb23 =>
                                                                                          cases ha ha1 ha2 with
                                                                                          | intro a3 hajoin =>
                                                                                              cases hajoin with
                                                                                              | intro ha13 ha23 =>
                                                                                                  exact
                                                                                                    Exists.intro
                                                                                                      (substitute 0 a3 b3)
                                                                                                      (And.intro
                                                                                                        (hsubst ha13 hb13)
                                                                                                        (hsubst ha23 hb23))

theorem betaParallel_diamond_from_substitution
    (hsubst : BetaParallelSubstitutionCompatibility)
    {t u v : Term}
    (h1 : BetaParallel t u)
    (h2 : BetaParallel t v) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  induction t generalizing u v with
  | var i =>
      exact betaParallel_diamond_var h1 h2
  | sort =>
      exact betaParallel_diamond_sort h1 h2
  | pi d c ihd ihc =>
      exact betaParallel_pi_shape_diamond h1 h2 ihd ihc
  | lam d b ihd ihb =>
      exact betaParallel_lam_shape_diamond h1 h2 ihd ihb
  | app f a ihf iha =>
      exact
        betaParallel_app_shape_diamond_from_substitution
          hsubst h1 h2 ihf iha

end BEDC.MetaCIC
