import BEDC.MetaCIC.Confluence.ClosedGeneral
import BEDC.MetaCIC.Confluence.ClosedUnconditional
import BEDC.MetaCIC.Confluence.Diamond
import BEDC.MetaCIC.Substitution.ClosedComposition
import BEDC.MetaCIC.ClosurePreservation

namespace BEDC.MetaCIC

def BetaParallelDiamondClosedAt : Prop :=
  ∀ {n : Idx} {t u v : Term},
    ClosedAt n t →
    BetaParallel t u →
    BetaParallel t v →
    ∃ w, BetaParallel u w ∧ BetaParallel v w

def BetaParallelClosedSubstitutionCompatibilityAt : Prop :=
  ∀ {n : Idx} {a a' b b' : Term},
    ClosedAt n a →
    ClosedAt (n + 1) b →
    BetaParallel a a' →
    BetaParallel b b' →
    BetaParallel (substitute 0 a b) (substitute 0 a' b')

theorem betaParallel_diamond_closed_at_to_closed
    (hdiamond : BetaParallelDiamondClosedAt) :
    BetaParallelDiamondClosed := by
  intro t u v hclosed htu htv
  exact hdiamond hclosed htu htv

theorem betaParallel_closed_substitution_composition_step
    (v u t : Term)
    (hv : ClosedAt 0 v) (hu : ClosedAt 0 u)
    (ht : ClosedAt 1 t) :
    BetaParallel
      (substitute 0 v (substitute 0 u t))
      (substitute 0 (substitute 0 v u) t) := by
  rw [substitute_compose_closed_both v u t hv hu ht]
  exact betaParallel_refl (substitute 0 (substitute 0 v u) t)

theorem betaParallel_closed_at_sort_diamond
    {u v : Term}
    (h1 : BetaParallel Term.sort u)
    (h2 : BetaParallel Term.sort v) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  exact betaParallel_diamond_sort h1 h2

theorem betaParallel_closed_at_var_diamond
    {n i : Idx} {u v : Term}
    (_hclosed : ClosedAt n (Term.var i))
    (h1 : BetaParallel (Term.var i) u)
    (h2 : BetaParallel (Term.var i) v) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  exact betaParallel_diamond_var h1 h2

theorem betaParallel_closed_at_pi_shape_diamond
    {n : Idx} {d c u v : Term}
    (_hclosed : ClosedAt n (Term.pi d c))
    (h1 : BetaParallel (Term.pi d c) u)
    (h2 : BetaParallel (Term.pi d c) v)
    (hd :
      ∀ {d1 d2 : Term},
        ClosedAt n d →
        BetaParallel d d1 →
        BetaParallel d d2 →
        ∃ e, BetaParallel d1 e ∧ BetaParallel d2 e)
    (hc :
      ∀ {c1 c2 : Term},
        ClosedAt (n + 1) c →
        BetaParallel c c1 →
        BetaParallel c c2 →
        ∃ r, BetaParallel c1 r ∧ BetaParallel c2 r) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  cases h1 with
  | pi hd1 hc1 =>
      cases h2 with
      | pi hd2 hc2 =>
          cases _hclosed with
          | piClosed hcd hcc =>
              cases hd hcd hd1 hd2 with
              | intro d3 hdjoin =>
                  cases hdjoin with
                  | intro hd13 hd23 =>
                      cases hc hcc hc1 hc2 with
                      | intro c3 hcjoin =>
                          cases hcjoin with
                          | intro hc13 hc23 =>
                              exact
                                Exists.intro (Term.pi d3 c3)
                                  (And.intro
                                    (BetaParallel.pi hd13 hc13)
                                    (BetaParallel.pi hd23 hc23))

theorem betaParallel_closed_at_lam_shape_diamond
    {n : Idx} {d b u v : Term}
    (_hclosed : ClosedAt n (Term.lam d b))
    (h1 : BetaParallel (Term.lam d b) u)
    (h2 : BetaParallel (Term.lam d b) v)
    (hd :
      ∀ {d1 d2 : Term},
        ClosedAt n d →
        BetaParallel d d1 →
        BetaParallel d d2 →
        ∃ e, BetaParallel d1 e ∧ BetaParallel d2 e)
    (hb :
      ∀ {b1 b2 : Term},
        ClosedAt (n + 1) b →
        BetaParallel b b1 →
        BetaParallel b b2 →
        ∃ c, BetaParallel b1 c ∧ BetaParallel b2 c) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  cases h1 with
  | lam hd1 hb1 =>
      cases h2 with
      | lam hd2 hb2 =>
          cases _hclosed with
          | lamClosed hcd hcb =>
              cases hd hcd hd1 hd2 with
              | intro d3 hdjoin =>
                  cases hdjoin with
                  | intro hd13 hd23 =>
                      cases hb hcb hb1 hb2 with
                      | intro b3 hbjoin =>
                          cases hbjoin with
                          | intro hb13 hb23 =>
                              exact
                                Exists.intro (Term.lam d3 b3)
                                  (And.intro
                                    (BetaParallel.lam hd13 hb13)
                                    (BetaParallel.lam hd23 hb23))

theorem betaParallel_closed_at_app_cong_cong_diamond
    {n : Idx} {f a f1 a1 f2 a2 : Term}
    (_hclosed : ClosedAt n (Term.app f a))
    (hf1 : BetaParallel f f1)
    (hf2 : BetaParallel f f2)
    (ha1 : BetaParallel a a1)
    (ha2 : BetaParallel a a2)
    (hf :
      ∀ {g1 g2 : Term},
        ClosedAt n f →
        BetaParallel f g1 →
        BetaParallel f g2 →
        ∃ g, BetaParallel g1 g ∧ BetaParallel g2 g)
    (ha :
      ∀ {b1 b2 : Term},
        ClosedAt n a →
        BetaParallel a b1 →
        BetaParallel a b2 →
        ∃ b, BetaParallel b1 b ∧ BetaParallel b2 b) :
    ∃ w,
      BetaParallel (Term.app f1 a1) w ∧
        BetaParallel (Term.app f2 a2) w := by
  cases _hclosed with
  | appClosed hcf hca =>
      exact
        betaParallel_app_diamond_of_components
          (hf hcf hf1 hf2)
          (ha hca ha1 ha2)

theorem betaParallel_closed_at_app_shape_diamond_from_substitution
    (hsubst : BetaParallelClosedSubstitutionCompatibilityAt)
    {n : Idx} {f a u v : Term}
    (hclosed : ClosedAt n (Term.app f a))
    (h1 : BetaParallel (Term.app f a) u)
    (h2 : BetaParallel (Term.app f a) v)
    (hf :
      ∀ {g1 g2 : Term},
        ClosedAt n f →
        BetaParallel f g1 →
        BetaParallel f g2 →
        ∃ g, BetaParallel g1 g ∧ BetaParallel g2 g)
    (ha :
      ∀ {b1 b2 : Term},
        ClosedAt n a →
        BetaParallel a b1 →
        BetaParallel a b2 →
        ∃ b, BetaParallel b1 b ∧ BetaParallel b2 b) :
    ∃ w, BetaParallel u w ∧ BetaParallel v w := by
  cases hclosed with
  | appClosed hcf hca =>
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
                                                betaParallel_closed_at_app_cong_cong_diamond
                                                  (ClosedAt.appClosed hcf hca)
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
                                                  cases hf hcf hf1 hf2 with
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
                                                                          cases ha hca ha1 ha2 with
                                                                          | intro a3 hajoin =>
                                                                              cases hajoin with
                                                                              | intro ha13 ha23 =>
                                                                                  have ha2Closed :
                                                                                      ClosedAt n a2 :=
                                                                                    betaParallel_preserves_closed hca ha2
                                                                                  have hb2Closed :
                                                                                      ClosedAt (n + 1) b2 :=
                                                                                    betaParallel_lam_target_body_closed
                                                                                      hcf hf2
                                                                                  exact
                                                                                    Exists.intro
                                                                                      (substitute 0 a3 b3)
                                                                                      (And.intro
                                                                                        (BetaParallel.appBeta hf1g ha13)
                                                                                        (hsubst ha2Closed hb2Closed ha23 hb23))
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
                                                  cases hf hcf hf1 hf2 with
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
                                                                          cases ha hca ha1 ha2 with
                                                                          | intro a3 hajoin =>
                                                                              cases hajoin with
                                                                              | intro ha13 ha23 =>
                                                                                  have ha1Closed :
                                                                                      ClosedAt n a1 :=
                                                                                    betaParallel_preserves_closed hca ha1
                                                                                  have hb1Closed :
                                                                                      ClosedAt (n + 1) b1 :=
                                                                                    betaParallel_lam_target_body_closed
                                                                                      hcf hf1
                                                                                  exact
                                                                                    Exists.intro
                                                                                      (substitute 0 a3 b3)
                                                                                      (And.intro
                                                                                        (hsubst ha1Closed hb1Closed ha13 hb13)
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
                                                      cases hf hcf hf1 hf2 with
                                                      | intro g hg =>
                                                          cases hg with
                                                          | intro hlam1g hlam2g =>
                                                              have hLamLeftJoin :=
                                                                betaParallel_lam_inv hlam1g
                                                              cases hLamLeftJoin with
                                                              | intro d3 hd3pack =>
                                                                  cases hd3pack with
                                                                  | intro b3 hpack3 =>
                                                                      cases hpack3 with
                                                                      | intro hgEq hrest3 =>
                                                                          cases hrest3 with
                                                                          | intro _ hb13 =>
                                                                              cases hgEq
                                                                              have hLamRightJoin :=
                                                                                betaParallel_lam_inv hlam2g
                                                                              cases hLamRightJoin with
                                                                              | intro d4 hd4pack =>
                                                                                  cases hd4pack with
                                                                                  | intro b4 hpack4 =>
                                                                                      cases hpack4 with
                                                                                      | intro htargetEq hrest4 =>
                                                                                          cases htargetEq
                                                                                          cases hrest4 with
                                                                                          | intro _ hb23 =>
                                                                                              cases ha hca ha1 ha2 with
                                                                                              | intro a3 hajoin =>
                                                                                                  cases hajoin with
                                                                                                  | intro ha13 ha23 =>
                                                                                                      have ha1Closed :
                                                                                                          ClosedAt n a1 :=
                                                                                                        betaParallel_preserves_closed hca ha1
                                                                                                      have hb1Closed :
                                                                                                          ClosedAt (n + 1) b1 :=
                                                                                                        betaParallel_lam_target_body_closed
                                                                                                          hcf hf1
                                                                                                      have ha2Closed :
                                                                                                          ClosedAt n a2 :=
                                                                                                        betaParallel_preserves_closed hca ha2
                                                                                                      have hb2Closed :
                                                                                                          ClosedAt (n + 1) b2 :=
                                                                                                        betaParallel_lam_target_body_closed
                                                                                                          hcf hf2
                                                                                                      exact
                                                                                                        Exists.intro
                                                                                                          (substitute 0 a3 b3)
                                                                                                          (And.intro
                                                                                                            (hsubst ha1Closed hb1Closed ha13 hb13)
                                                                                                            (hsubst ha2Closed hb2Closed ha23 hb23))

theorem betaParallel_diamond_closed_at_from_substitution
    (hsubst : BetaParallelClosedSubstitutionCompatibilityAt) :
    BetaParallelDiamondClosedAt := by
  intro n t u v hclosed h1 h2
  induction t generalizing n u v with
  | var i =>
      exact betaParallel_closed_at_var_diamond hclosed h1 h2
  | sort =>
      exact betaParallel_closed_at_sort_diamond h1 h2
  | pi d c ihd ihc =>
      exact
        betaParallel_closed_at_pi_shape_diamond
          hclosed h1 h2
          (fun hcd hd1 hd2 => ihd hcd hd1 hd2)
          (fun hcc hc1 hc2 => ihc hcc hc1 hc2)
  | lam d b ihd ihb =>
      exact
        betaParallel_closed_at_lam_shape_diamond
          hclosed h1 h2
          (fun hcd hd1 hd2 => ihd hcd hd1 hd2)
          (fun hcb hb1 hb2 => ihb hcb hb1 hb2)
  | app f a ihf iha =>
      exact
        betaParallel_closed_at_app_shape_diamond_from_substitution
          hsubst hclosed h1 h2
          (fun hcf hf1 hf2 => ihf hcf hf1 hf2)
          (fun hca ha1 ha2 => iha hca ha1 ha2)

theorem betaStarStep_confluence_closed_general_of_context_substitution
    (hsubst : BetaParallelClosedSubstitutionCompatibilityAt)
    {t u v : Term} (hclosed : ClosedAt 0 t)
    (h1 : BetaStarStep t u) (h2 : BetaStarStep t v) :
    ∃ w, BetaStarStep u w ∧ BetaStarStep v w := by
  exact
    betaStarStep_confluence_general_of_parallel_diamond_closed
      (betaParallel_diamond_closed_at_to_closed
        (betaParallel_diamond_closed_at_from_substitution hsubst))
      hclosed h1 h2

theorem betaStarStep_confluence_closed_general_from_closed_diamond
    {t u v : Term} (hclosed : ClosedAt 0 t)
    (hdiamond : BetaParallelDiamondClosedAt)
    (h1 : BetaStarStep t u) (h2 : BetaStarStep t v) :
    ∃ w, BetaStarStep u w ∧ BetaStarStep v w := by
  exact
    betaStarStep_confluence_general_of_parallel_diamond_closed
      (betaParallel_diamond_closed_at_to_closed hdiamond)
      hclosed h1 h2

end BEDC.MetaCIC
