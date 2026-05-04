import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_finite_prefix_transported_endpoint_denominator_package
    {x x' y z z' : Nat -> BHist} {n : Nat} :
    RealStreamClassifier x y -> RealStreamClassifier y z -> hsame (x n) (x' n) ->
      hsame (z n) (z' n) ->
        RatHistoryClassifier (x' n) (z' n) ∧
          PositiveUnaryDenominator (x' n) ∧
            PositiveUnaryDenominator (z' n) ∧
              UnaryHistory (x' n) ∧ UnaryHistory (z' n) ∧
                (hsame (x' n) BHist.Empty -> False) ∧
                  (hsame (z' n) BHist.Empty -> False) := by
  intro classifiedXY classifiedYZ sameLeft sameRight
  have classifiedXZ : RealStreamClassifier x z :=
    RealStreamClassifier_trans classifiedXY classifiedYZ
  have transported : RatHistoryClassifier (x' n) (z' n) :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight (classifiedXZ n)
  have positiveRows :
      PositiveUnaryDenominator (x' n) ∧ PositiveUnaryDenominator (z' n) :=
    RatHistoryClassifier_positive_denominators transported
  have leftRows : UnaryHistory (x' n) ∧ (hsame (x' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.left
  have rightRows : UnaryHistory (z' n) ∧ (hsame (z' n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.right
  exact And.intro transported
    (And.intro positiveRows.left
      (And.intro positiveRows.right
        (And.intro leftRows.left
          (And.intro rightRows.left
            (And.intro leftRows.right rightRows.right)))))

end BEDC.Derived.RealUp
