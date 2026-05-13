import BEDC.MetaCIC.Confluence.ClosedUnconditional
import BEDC.MetaCIC.Confluence.Diamond
import BEDC.MetaCIC.ClosurePreservation
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

def BetaParallelDiamondClosed : Prop :=
  ∀ {t u v : Term},
    ClosedAt 0 t →
    BetaParallel t u →
    BetaParallel t v →
    ∃ w, BetaParallel u w ∧ BetaParallel v w

def BetaParallelClosedStrip : Prop :=
  ∀ {t u v : Term},
    ClosedAt 0 t →
    BetaParallel t u →
    BetaStarStep t v →
    ∃ w, BetaStarStep u w ∧ BetaParallel v w

def BetaParallelClosedSubstitutionCompatibility : Prop :=
  ∀ {a a' b b' : Term},
    ClosedAt 0 a →
    ClosedAt 1 b →
    BetaParallel a a' →
    BetaParallel b b' →
    BetaParallel (substitute 0 a b) (substitute 0 a' b')

theorem betaParallel_closed_substitution_compatibility_obstruction :
    substitute 0 (Term.var 0)
        (substitute 0 Term.sort (Term.var 1)) ≠
      substitute 0 (substitute 0 (Term.var 0) Term.sort)
        (substitute 1 (Term.var 0) (Term.var 1)) := by
  exact substitute_commutation_unclosed_obstruction

theorem betaParallel_closed_strip_of_diamond
    (hdiamond : BetaParallelDiamondClosed)
    {t u v : Term}
    (hclosed : ClosedAt 0 t)
    (hpar : BetaParallel t u)
    (hstar : BetaStarStep t v) :
    ∃ w, BetaStarStep u w ∧ BetaParallel v w := by
  induction hstar generalizing u with
  | refl t =>
      exact
        Exists.intro u
          (And.intro
            (BetaStarStep.refl u)
            hpar)
  | step hstep htail ih =>
      have hmidClosed := betaStep_preserves_closed hclosed hstep
      have hstepPar := betaStep_to_parallel hstep
      cases hdiamond hclosed hpar hstepPar with
      | intro x hx =>
          cases hx with
          | intro hux hsteppedx =>
              cases ih hmidClosed hsteppedx with
              | intro w hw =>
                  cases hw with
                  | intro hxw hvw =>
                      exact
                        Exists.intro w
                          (And.intro
                            (betaStar_trans (betaParallel_to_betaStar hux) hxw)
                            hvw)

theorem betaParallel_closed_strip_from_diamond
    (hdiamond : BetaParallelDiamondClosed) :
    BetaParallelClosedStrip := by
  intro t u v hclosed hpar hstar
  exact betaParallel_closed_strip_of_diamond hdiamond hclosed hpar hstar

theorem betaStarStep_confluence_general_of_parallel_diamond_closed
    (hdiamond : BetaParallelDiamondClosed)
    {t u v : Term}
    (hclosed : ClosedAt 0 t)
    (h1 : BetaStarStep t u) (h2 : BetaStarStep t v) :
    ∃ w, BetaStarStep u w ∧ BetaStarStep v w := by
  induction h1 generalizing v with
  | refl t =>
      exact
        Exists.intro v
          (And.intro
            h2
            (BetaStarStep.refl v))
  | step hstep htail ih =>
      have hmidClosed := betaStep_preserves_closed hclosed hstep
      have hstepPar := betaStep_to_parallel hstep
      cases
        betaParallel_closed_strip_of_diamond
          hdiamond hclosed hstepPar h2 with
      | intro x hx =>
          cases hx with
          | intro hux hvxPar =>
              cases ih hmidClosed hux with
              | intro w hw =>
                  cases hw with
                  | intro htargetw hxw =>
                      exact
                        Exists.intro w
                          (And.intro
                            htargetw
                            (betaStar_trans (betaParallel_to_betaStar hvxPar) hxw))

theorem betaStarStep_confluence_closed_lam_of_normal
    {d b u v : Term}
    (hclosed : ClosedAt 0 (Term.lam d b))
    (hnormal : BetaNormal (Term.lam d b))
    (h1 : BetaStarStep (Term.lam d b) u)
    (h2 : BetaStarStep (Term.lam d b) v) :
    ∃ w, BetaStarStep u w ∧ BetaStarStep v w := by
  exact betaStarStep_confluence_closed_normal hclosed hnormal h1 h2

end BEDC.MetaCIC
