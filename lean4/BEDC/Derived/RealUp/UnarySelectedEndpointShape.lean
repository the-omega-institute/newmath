import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp
open BEDC.Derived.StreamNameUp

theorem RealUnaryStreamClassifier_transported_selected_endpoint_shape_package
    {s t s' t' : BHist -> BHist} {n a b zS zT : BHist} :
    UnaryHistory n -> RealUnaryStreamClassifier s t ->
      (forall k : BHist, UnaryHistory k -> hsame (s k) (s' k)) ->
        (forall k : BHist, UnaryHistory k -> hsame (t k) (t' k)) ->
          hsame (s' n) (BHist.e1 a) -> hsame (t' n) (BHist.e1 b) ->
            RatHistoryClassifier (s' n) (t' n) ∧ PositiveUnaryDenominator (s' n) ∧
              PositiveUnaryDenominator (t' n) ∧ UnaryHistory (s' n) ∧
                UnaryHistory (t' n) ∧ (hsame (s' n) BHist.Empty -> False) ∧
                  (hsame (t' n) BHist.Empty -> False) ∧
                    (hsame (s' n) (BHist.e0 zS) -> False) ∧
                      (hsame (t' n) (BHist.e0 zT) -> False) ∧
                        UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  intro nUnary classified sameS sameT sameS'E1 sameT'E1
  have transported : RatHistoryClassifier (s' n) (t' n) :=
    RatHistoryClassifier_hsame_transport (sameS n nUnary) (sameT n nUnary)
      (classified n nUnary)
  have displayed : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameS'E1 sameT'E1 transported
  have tailReadback : UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayed
  have positives :
      PositiveUnaryDenominator (s' n) ∧ PositiveUnaryDenominator (t' n) :=
    RatHistoryClassifier_positive_denominators transported
  have leftRows :
      UnaryHistory (s' n) ∧ (hsame (s' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows :
      UnaryHistory (t' n) ∧ (hsame (t' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact And.intro transported
    (And.intro positives.left
      (And.intro positives.right
        (And.intro leftRows.left
          (And.intro rightRows.left
            (And.intro leftRows.right
              (And.intro rightRows.right
                (And.intro
                  (fun sameZero =>
                    PositiveUnaryDenominator_e0_absurd
                      (PositiveUnaryDenominator_hsame_transport sameZero positives.left))
                  (And.intro
                    (fun sameZero =>
                      PositiveUnaryDenominator_e0_absurd
                        (PositiveUnaryDenominator_hsame_transport sameZero positives.right))
                    tailReadback))))))))

theorem RatStreamNameClassifier_selected_endpoint_tail_pairwise_coherence
    {s t s' t' : BHist -> BHist} {n a a' b b' : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n ->
      (forall k : BHist, UnaryHistory k -> hsame (s k) (s' k)) ->
      (forall k : BHist, UnaryHistory k -> hsame (t k) (t' k)) ->
      hsame (s' n) (BHist.e1 a) -> hsame (s' n) (BHist.e1 a') ->
      hsame (t' n) (BHist.e1 b) -> hsame (t' n) (BHist.e1 b') ->
        UnaryHistory a ∧ UnaryHistory a' ∧ UnaryHistory b ∧ UnaryHistory b' ∧
          hsame a a' ∧ hsame a b ∧ hsame a b' ∧ hsame a' b ∧ hsame a' b' ∧
            hsame b b' := by
  intro classified nUnary sameS sameT sameSA sameSA' sameTB sameTB'
  have transported : RatHistoryClassifier (s' n) (t' n) :=
    RatHistoryClassifier_hsame_transport (sameS n nUnary) (sameT n nUnary)
      (classified.right.right n nUnary)
  have displayedAB : RatHistoryClassifier (BHist.e1 a) (BHist.e1 b) :=
    RatHistoryClassifier_hsame_transport sameSA sameTB transported
  have displayedA'B' : RatHistoryClassifier (BHist.e1 a') (BHist.e1 b') :=
    RatHistoryClassifier_hsame_transport sameSA' sameTB' transported
  have tailsAB : UnaryHistory a ∧ UnaryHistory b ∧ hsame a b :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayedAB
  have tailsA'B' : UnaryHistory a' ∧ UnaryHistory b' ∧ hsame a' b' :=
    RatHistoryClassifier_e1_tail_unary_iff.mp displayedA'B'
  have sameAA' : hsame a a' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameSA) sameSA')
  have sameBB' : hsame b b' :=
    hsame_e1_iff.mp (hsame_trans (hsame_symm sameTB) sameTB')
  have sameAB' : hsame a b' :=
    hsame_trans tailsAB.right.right sameBB'
  have sameA'B : hsame a' b :=
    hsame_trans (hsame_symm sameAA') tailsAB.right.right
  exact And.intro tailsAB.left
    (And.intro tailsA'B'.left
      (And.intro tailsAB.right.left
        (And.intro tailsA'B'.right.left
          (And.intro sameAA'
            (And.intro tailsAB.right.right
              (And.intro sameAB'
                  (And.intro sameA'B
                    (And.intro tailsA'B'.right.right sameBB'))))))))

theorem RatStreamNameClassifier_selected_endpoint_denominator_package
    {s t : BHist -> BHist} {n zS zT : BHist} :
    RatStreamNameClassifier s t -> UnaryHistory n ->
      RatHistoryClassifier (s n) (t n) ∧ PositiveUnaryDenominator (s n) ∧
        PositiveUnaryDenominator (t n) ∧ UnaryHistory (s n) ∧ UnaryHistory (t n) ∧
          (hsame (s n) BHist.Empty -> False) ∧
            (hsame (t n) BHist.Empty -> False) ∧
              (hsame (s n) (BHist.e0 zS) -> False) ∧
                (hsame (t n) (BHist.e0 zT) -> False) := by
  intro classified nUnary
  have pointClassified : RatHistoryClassifier (s n) (t n) :=
    classified.right.right n nUnary
  have shape :=
    RatStreamNameClassifier_observation_shape_exclusions (s := s) (t := t) (n := n)
      classified nUnary
  exact And.intro pointClassified
    (And.intro shape.left
      (And.intro shape.right.left
        (And.intro shape.right.right.left
          (And.intro shape.right.right.right.left
            (And.intro shape.right.right.right.right.left
              (And.intro shape.right.right.right.right.right.left
                (And.intro (shape.right.right.right.right.right.right.left zS)
                  (shape.right.right.right.right.right.right.right zT))))))))

end BEDC.Derived.RealUp
