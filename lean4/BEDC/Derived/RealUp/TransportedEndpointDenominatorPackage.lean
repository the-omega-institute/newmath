import BEDC.Derived.RealUp
import BEDC.Derived.RealUp.PrefixTailExtension

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

theorem RealStreamPrefixClassifier_finite_tail_transported_endpoint_denominator_package
    {x y : Nat -> BHist} {n m : Nat} {u v : BHist} :
    RealStreamPrefixClassifier x y n ->
      (forall k : Nat, k < m ->
        RatHistoryClassifier (x (n + Nat.succ k)) (y (n + Nat.succ k))) ->
        (forall i : Nat, UnaryHistory (x i)) -> hsame (x (n + m)) u ->
          hsame (y (n + m)) v ->
            RatHistoryClassifier u v ∧
              PositiveUnaryDenominator u ∧
                PositiveUnaryDenominator v ∧
                  UnaryHistory u ∧ UnaryHistory v ∧
                    (hsame u BHist.Empty -> False) ∧
                      (hsame v BHist.Empty -> False) := by
  intro basePrefix tail unary sameLeft sameRight
  have extended :
      RealStreamPrefixClassifier x y (n + m) ∧ UnaryHistory (x (n + m)) :=
    RealStreamPrefixClassifier_tail_extension_with_unary_anchor (x := x) (y := y) n m
      basePrefix tail unary
  have endpointClassified : RatHistoryClassifier (x (n + m)) (y (n + m)) :=
    RealStreamPrefixClassifier_endpoint (n + m) extended.left
  have transported : RatHistoryClassifier u v :=
    RatHistoryClassifier_hsame_transport sameLeft sameRight endpointClassified
  have positiveRows : PositiveUnaryDenominator u ∧ PositiveUnaryDenominator v :=
    RatHistoryClassifier_positive_denominators transported
  have leftRows : UnaryHistory u ∧ (hsame u BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.left
  have rightRows : UnaryHistory v ∧ (hsame v BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positiveRows.right
  exact And.intro transported
    (And.intro positiveRows.left
      (And.intro positiveRows.right
        (And.intro leftRows.left
          (And.intro rightRows.left
            (And.intro leftRows.right rightRows.right)))))

end BEDC.Derived.RealUp
