import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

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

end BEDC.Derived.RealUp
