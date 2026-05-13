import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Confluence.ClosedUnconditional
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.SubjectReduction.ClosedDischarge
import BEDC.MetaCIC.SubjectReduction.ClosedBinderDischarge
import BEDC.MetaCIC.Normalization.Reducibility

namespace BEDC.MetaCIC

def BetaConv (t u : Term) : Prop :=
  ∃ w, BetaStarStep t w ∧ BetaStarStep u w

theorem BetaConv.refl (t : Term) : BetaConv t t := by
  exact
    Exists.intro t
      (And.intro
        (BetaStarStep.refl t)
        (BetaStarStep.refl t))

theorem BetaConv.symm {t u : Term} (h : BetaConv t u) : BetaConv u t := by
  cases h with
  | intro w hw =>
      cases hw with
      | intro htw huw =>
          exact Exists.intro w (And.intro huw htw)

theorem BetaConv.of_betaStar_left {t u : Term}
    (h : BetaStarStep t u) :
    BetaConv t u := by
  exact
    Exists.intro u
      (And.intro h (BetaStarStep.refl u))

theorem BetaConv.of_betaStar_right {t u : Term}
    (h : BetaStarStep u t) :
    BetaConv t u := by
  exact
    Exists.intro t
      (And.intro (BetaStarStep.refl t) h)

theorem BetaConv.of_betaStep_left {t u : Term}
    (h : BetaStep t u) :
    BetaConv t u := by
  exact BetaConv.of_betaStar_left (betaStar_one h)

theorem BetaConv.of_betaStep_right {t u : Term}
    (h : BetaStep u t) :
    BetaConv t u := by
  exact BetaConv.of_betaStar_right (betaStar_one h)

theorem BetaConv.trans_of_confluence {t u v : Term}
    (hconf :
      ∀ {x y z : Term},
        BetaStarStep x y →
        BetaStarStep x z →
        ∃ q, BetaStarStep y q ∧ BetaStarStep z q)
    (h1 : BetaConv t u) (h2 : BetaConv u v) :
    BetaConv t v := by
  cases h1 with
  | intro w1 hw1 =>
      cases hw1 with
      | intro htw1 huw1 =>
          cases h2 with
          | intro w2 hw2 =>
              cases hw2 with
              | intro huw2 hvw2 =>
                  cases hconf huw1 huw2 with
                  | intro q hq =>
                      cases hq with
                      | intro hw1q hw2q =>
                          exact
                            Exists.intro q
                              (And.intro
                                (betaStar_trans htw1 hw1q)
                                (betaStar_trans hvw2 hw2q))

theorem betaNormal_of_betaStrong {t : Term}
    (h : BetaStrong t) :
    BetaNormal t := by
  intro u hstep
  exact betaStrong_no_step h hstep

theorem BetaConv.trans_normal_middle {t u v : Term}
    (huN : BetaStrong u)
    (h1 : BetaConv t u) (h2 : BetaConv u v) :
    BetaConv t v := by
  cases h1 with
  | intro w1 hw1 =>
      cases hw1 with
      | intro htw1 huw1 =>
          cases h2 with
          | intro w2 hw2 =>
              cases hw2 with
              | intro huw2 hvw2 =>
                  have hw1eq : w1 = u := by
                    exact betaStarStep_eq_of_betaNormal
                      (betaNormal_of_betaStrong huN) huw1
                  have hw2eq : w2 = u := by
                    exact betaStarStep_eq_of_betaNormal
                      (betaNormal_of_betaStrong huN) huw2
                  cases hw1eq
                  cases hw2eq
                  exact Exists.intro u (And.intro htw1 hvw2)

theorem BetaConv.trans_closed_normal_middle {t u v : Term}
    (_ht : ClosedAt 0 t) (_hu : ClosedAt 0 u) (_hv : ClosedAt 0 v)
    (huN : BetaStrong u)
    (h1 : BetaConv t u) (h2 : BetaConv u v) :
    BetaConv t v := by
  exact BetaConv.trans_normal_middle huN h1 h2

theorem BetaConv_normal_forms_equal_closed
    {t u : Term}
    (_htC : ClosedAt 0 t) (_huC : ClosedAt 0 u)
    (htN : BetaStrong t) (huN : BetaStrong u)
    (h : BetaConv t u) : t = u := by
  cases h with
  | intro w hw =>
      cases hw with
      | intro htw huw =>
          have hwt : w = t := by
            exact betaStarStep_eq_of_betaNormal
              (betaNormal_of_betaStrong htN) htw
          have hwu : w = u := by
            exact betaStarStep_eq_of_betaNormal
              (betaNormal_of_betaStrong huN) huw
          cases hwt
          cases hwu
          rfl

def HasTypeBetaConvInvariantClosedStatement : Prop :=
  ∀ {t u A : Term},
    ClosedAt 0 t →
    ClosedAt 0 u →
    HasType [] t A →
    BetaConv t u →
    HasType [] u A

theorem closedLamDomainTarget_closed :
    ClosedAt 0 closedLamDomainTarget := by
  unfold closedLamDomainTarget
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.varClosed
    exact Nat.zero_lt_succ 0

theorem BetaConv_closed_lam_domain_type_obstruction :
    ∃ t, ∃ u, ∃ A,
      ClosedAt 0 t ∧
        ClosedAt 0 u ∧
          HasType [] t A ∧
            BetaConv t u ∧
              ¬ HasType [] u A := by
  exact
    Exists.intro closedLamDomainSource
      (Exists.intro closedLamDomainTarget
        (Exists.intro closedLamDomainType
          (And.intro
            closedLamDomainSource_closed
            (And.intro
              closedLamDomainTarget_closed
              (And.intro
                closedLamDomainSource_typed
                (And.intro
                  (BetaConv.of_betaStep_left closedLamDomainSource_step)
                  closedLamDomainTarget_not_typed))))))

theorem not_HasType_BetaConv_invariant_closed :
    ¬ HasTypeBetaConvInvariantClosedStatement := by
  intro h
  exact closedLamDomainTarget_not_typed
    (h
      closedLamDomainSource_closed
      closedLamDomainTarget_closed
      closedLamDomainSource_typed
      (BetaConv.of_betaStep_left closedLamDomainSource_step))

end BEDC.MetaCIC
