import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_finite_prefix_endpoint_denominator_package
    {x y z : Nat -> BHist} {n : Nat} :
    (forall i : Nat, RatHistoryCarrier (x i)) ->
      RealStreamClassifier x y -> RealStreamClassifier y z ->
        RealStreamPrefixClassifier x x n ∧ RealStreamPrefixClassifier y x n ∧
          RealStreamPrefixClassifier x z n ∧ RatHistoryClassifier (x n) (z n) ∧
            PositiveUnaryDenominator (x n) ∧ PositiveUnaryDenominator (z n) ∧
              UnaryHistory (x n) ∧ UnaryHistory (z n) ∧
                (hsame (x n) BHist.Empty -> False) ∧
                  (hsame (z n) BHist.Empty -> False) := by
  intro carrierX classifiedXY classifiedYZ
  have prefixXX : RealStreamPrefixClassifier x x n :=
    RealStreamPrefixClassifier_refl carrierX n
  have prefixXY : RealStreamPrefixClassifier x y n :=
    RealStreamClassifier_prefix classifiedXY n
  have prefixYX : RealStreamPrefixClassifier y x n :=
    RealStreamPrefixClassifier_symm n prefixXY
  have prefixYZ : RealStreamPrefixClassifier y z n :=
    RealStreamClassifier_prefix classifiedYZ n
  have prefixXZ : RealStreamPrefixClassifier x z n :=
    RealStreamPrefixClassifier_trans n prefixXY prefixYZ
  have endpointXZ : RatHistoryClassifier (x n) (z n) :=
    RealStreamPrefixClassifier_endpoint n prefixXZ
  have positives : PositiveUnaryDenominator (x n) ∧ PositiveUnaryDenominator (z n) :=
    RatHistoryClassifier_positive_denominators endpointXZ
  have leftRows : UnaryHistory (x n) ∧ (hsame (x n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows : UnaryHistory (z n) ∧ (hsame (z n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact And.intro prefixXX
    (And.intro prefixYX
      (And.intro prefixXZ
        (And.intro endpointXZ
          (And.intro positives.left
            (And.intro positives.right
              (And.intro leftRows.left
                (And.intro rightRows.left
                  (And.intro leftRows.right rightRows.right))))))))

end BEDC.Derived.RealUp
