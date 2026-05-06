import BEDC.Derived.StreamNameUp

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamNameClassifier_observation_full_endpoint_package {s t : BHist -> BHist}
    {n a b z_s z_t : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n -> hsame (s n) (BHist.e1 a) ->
      hsame (t n) (BHist.e1 b) ->
        RatHistoryClassifier (s n) (t n) ∧ PositiveUnaryDenominator (s n) ∧
          PositiveUnaryDenominator (t n) ∧ UnaryHistory (s n) ∧ UnaryHistory (t n) ∧
            (hsame (s n) BHist.Empty -> False) ∧
              (hsame (t n) BHist.Empty -> False) ∧
                (hsame (s n) (BHist.e0 z_s) -> False) ∧
                  (hsame (t n) (BHist.e0 z_t) -> False) ∧
                    UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro classified nUnary sameLeft sameRight
  have pointClassified : RatHistoryClassifier (s n) (t n) :=
    classified.right.right n nUnary
  have shape :=
    RatStreamNameClassifier_observation_shape_exclusions (s := s) (t := t) (n := n)
      classified nUnary
  have tails :=
    RatStreamNameClassifier_observation_e1_pair_readback (s := s) (t := t) (n := n)
      (a := a) (b := b) classified nUnary sameLeft sameRight
  exact And.intro pointClassified
    (And.intro shape.left
      (And.intro shape.right.left
        (And.intro shape.right.right.left
          (And.intro shape.right.right.right.left
            (And.intro shape.right.right.right.right.left
              (And.intro shape.right.right.right.right.right.left
                (And.intro (shape.right.right.right.right.right.right.left z_s)
                  (And.intro (shape.right.right.right.right.right.right.right z_t)
                    tails))))))))

theorem RatStreamNameFiniteWindowClassifier_exhausts_classifier {s t : BHist -> BHist} :
    RatStreamNameClassifier s t ↔
      (forall n : BHist, UnaryHistory n ->
        RatStreamNameFiniteWindowClassifier s t
          (ProbeBundle.Bcons n ProbeBundle.Bnil)) := by
  constructor
  · intro classified n _nUnary m _member mUnary
    exact classified.right.right m mUnary
  · intro windowClassified
    have carrierS : RatStreamNameCarrier s := by
      intro n nUnary
      have pointClassified :=
        windowClassified n nUnary n (inBundle_cons_self n ProbeBundle.Bnil) nUnary
      exact pointClassified.left
    have carrierT : RatStreamNameCarrier t := by
      intro n nUnary
      have pointClassified :=
        windowClassified n nUnary n (inBundle_cons_self n ProbeBundle.Bnil) nUnary
      exact pointClassified.right.left
    have pointRows :
        forall n : BHist, UnaryHistory n -> RatHistoryClassifier (s n) (t n) := by
      intro n nUnary
      exact windowClassified n nUnary n (inBundle_cons_self n ProbeBundle.Bnil) nUnary
    exact And.intro carrierS (And.intro carrierT pointRows)

end BEDC.Derived.StreamNameUp
