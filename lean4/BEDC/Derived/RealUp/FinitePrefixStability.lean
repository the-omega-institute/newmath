import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RealStreamClassifier_finite_prefix_unary_stability_package
    {x y z : Nat -> BHist} {n : Nat} :
    (forall i : Nat, RatHistoryCarrier (x i)) -> RealStreamClassifier x y ->
      RealStreamClassifier y z ->
        RealStreamPrefixClassifier x x n ∧ RealStreamPrefixClassifier y x n ∧
          RealStreamPrefixClassifier x z n ∧ RatHistoryClassifier (x n) (z n) ∧
            UnaryHistory (x n) ∧ UnaryHistory (z n) := by
  intro xCarrier classifiedXY classifiedYZ
  have prefixXX : RealStreamPrefixClassifier x x n :=
    RealStreamPrefixClassifier_refl xCarrier n
  have prefixYX : RealStreamPrefixClassifier y x n :=
    RealStreamClassifier_prefix (RealStreamClassifier_symm classifiedXY) n
  have streamXZ : RealStreamClassifier x z :=
    RealStreamClassifier_trans classifiedXY classifiedYZ
  have prefixXZ : RealStreamPrefixClassifier x z n :=
    RealStreamClassifier_prefix streamXZ n
  have endpointXZ : RatHistoryClassifier (x n) (z n) :=
    RealStreamPrefixClassifier_endpoint n prefixXZ
  have positives : PositiveUnaryDenominator (x n) ∧ PositiveUnaryDenominator (z n) :=
    RatHistoryClassifier_positive_denominators endpointXZ
  exact And.intro prefixXX
    (And.intro prefixYX
      (And.intro prefixXZ
        (And.intro endpointXZ
          (And.intro (PositiveUnaryDenominator_unary_and_nonempty positives.left).left
            (PositiveUnaryDenominator_unary_and_nonempty positives.right).left))))

end BEDC.Derived.RealUp
