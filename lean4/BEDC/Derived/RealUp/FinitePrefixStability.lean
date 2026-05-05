import BEDC.Derived.RealUp
import BEDC.Derived.RealUp.PrefixTailExtension

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

theorem RealStreamPrefixClassifier_add_left_endpoint_positive_unary_nonempty_package
    {x y : Nat -> BHist} {n m : Nat} :
    (forall i : Nat, UnaryHistory (x i)) -> RealStreamPrefixClassifier x y (m + n) ->
      PositiveUnaryDenominator (x n) ∧ PositiveUnaryDenominator (y n) ∧
        UnaryHistory (x n) ∧ UnaryHistory (y n) ∧
          (hsame (x n) BHist.Empty -> False) ∧
            (hsame (y n) BHist.Empty -> False) := by
  intro unary classified
  have prefixAtN :
      RealStreamPrefixClassifier x y n ∧ UnaryHistory (x n) :=
    RealStreamPrefixClassifier_add_left_previous_with_unary unary n m classified
  have endpointClassified : RatHistoryClassifier (x n) (y n) :=
    RealStreamPrefixClassifier_endpoint n prefixAtN.left
  have positives :
      PositiveUnaryDenominator (x n) ∧ PositiveUnaryDenominator (y n) :=
    RatHistoryClassifier_positive_denominators endpointClassified
  have leftRows : UnaryHistory (x n) ∧ (hsame (x n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.left
  have rightRows : UnaryHistory (y n) ∧ (hsame (y n) BHist.Empty -> False) :=
    PositiveUnaryDenominator_unary_and_nonempty positives.right
  exact And.intro positives.left
    (And.intro positives.right
      (And.intro leftRows.left
        (And.intro rightRows.left (And.intro leftRows.right rightRows.right))))

theorem RealStreamPrefixClassifier_finite_window_zero_exactness {x y : Nat -> BHist} :
    forall m : Nat, RealStreamPrefixClassifier x y m <->
      (forall k : Nat, k <= m ->
        UnaryHistory (x k) /\ UnaryHistory (y k) /\ RatHistoryClassifier (x k) (y k)) := by
  intro m
  induction m with
  | zero =>
      constructor
      · intro classified k within
        cases k with
        | zero =>
            have positiveRows :
                PositiveUnaryDenominator (x Nat.zero) ∧ PositiveUnaryDenominator (y Nat.zero) :=
              RatHistoryClassifier_positive_denominators classified
            exact And.intro (PositiveUnaryDenominator_unary_and_nonempty positiveRows.left).left
              (And.intro
                (PositiveUnaryDenominator_unary_and_nonempty positiveRows.right).left classified)
        | succ k =>
            cases within
      · intro windowRows
        exact (windowRows Nat.zero (Nat.le_refl Nat.zero)).right.right
  | succ m ih =>
      constructor
      · intro classified k within
        cases k with
        | zero =>
            exact (Iff.mp ih classified.left) Nat.zero (Nat.zero_le m)
        | succ k =>
            have predWithin : k <= m := Nat.le_of_succ_le_succ within
            cases predWithin with
            | refl =>
                have positiveRows :
                    PositiveUnaryDenominator (x (Nat.succ m)) ∧
                      PositiveUnaryDenominator (y (Nat.succ m)) :=
                  RatHistoryClassifier_positive_denominators classified.right
                exact And.intro
                  (PositiveUnaryDenominator_unary_and_nonempty positiveRows.left).left
                  (And.intro
                    (PositiveUnaryDenominator_unary_and_nonempty positiveRows.right).left
                    classified.right)
            | step earlier =>
                exact (Iff.mp ih classified.left) (Nat.succ k) (Nat.succ_le_succ earlier)
      · intro windowRows
        constructor
        · exact Iff.mpr ih (fun k within =>
            windowRows k (Nat.le_trans within (Nat.le_succ m)))
        · exact (windowRows (Nat.succ m) (Nat.le_refl (Nat.succ m))).right.right

end BEDC.Derived.RealUp
