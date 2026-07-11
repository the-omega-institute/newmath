import BEDC.Derived.Window6WeightLogConcaveTuran

namespace BEDC
namespace Derived
namespace Window6WeightToeplitzTotalPositive

set_option maxRecDepth 10000

open Window6WeightLogConcaveTuran

/-!
Toeplitz total-positivity / Polya-frequency certificates for the
Fibonacci-cube weight coefficients.  Real-rootedness gives the
Aissen-Schoenberg-Whitney total-positivity strengthening of log-concavity,
equivalently a finite discrete Laguerre-Polya shadow.  This module records
finite Nat certificates for the Fibonacci carrier windows `m = 6, 7, 8, 9,
10`; it is not a proof of RH.
-/

def toeplitzTwoMinorNonnegative (m k : Nat) : Prop :=
  weightCoeff m (k + 2) * weightCoeff m k <=
    weightCoeff m (k + 1) * weightCoeff m (k + 1)

def toeplitzThreeNegative (m k : Nat) : Nat :=
  weightCoeff m (k + 4) * weightCoeff m (k + 2) * weightCoeff m k +
    weightCoeff m (k + 3) * weightCoeff m (k + 2) * weightCoeff m (k + 1) +
      weightCoeff m (k + 3) * weightCoeff m (k + 2) * weightCoeff m (k + 1)

def toeplitzThreePositive (m k : Nat) : Nat :=
  weightCoeff m (k + 2) * weightCoeff m (k + 2) * weightCoeff m (k + 2) +
    weightCoeff m (k + 3) * weightCoeff m (k + 3) * weightCoeff m k +
      weightCoeff m (k + 4) * weightCoeff m (k + 1) * weightCoeff m (k + 1)

def toeplitzThreeMinorNonnegative (m k : Nat) : Prop :=
  toeplitzThreeNegative m k <= toeplitzThreePositive m k

theorem toeplitz_two_six_zero : toeplitzTwoMinorNonnegative 6 0 :=
  Nat.le.intro (show weightCoeff 6 2 * weightCoeff 6 0 + 26 =
    weightCoeff 6 1 * weightCoeff 6 1 from rfl)

theorem toeplitz_two_six_one : toeplitzTwoMinorNonnegative 6 1 :=
  Nat.le.intro (show weightCoeff 6 3 * weightCoeff 6 1 + 76 =
    weightCoeff 6 2 * weightCoeff 6 2 from rfl)

theorem toeplitz_two_six_two : toeplitzTwoMinorNonnegative 6 2 :=
  Nat.le.intro (show weightCoeff 6 4 * weightCoeff 6 2 + 16 =
    weightCoeff 6 3 * weightCoeff 6 3 from rfl)

theorem toeplitz_two_seven_zero : toeplitzTwoMinorNonnegative 7 0 :=
  Nat.le.intro (show weightCoeff 7 2 * weightCoeff 7 0 + 34 =
    weightCoeff 7 1 * weightCoeff 7 1 from rfl)

theorem toeplitz_two_seven_one : toeplitzTwoMinorNonnegative 7 1 :=
  Nat.le.intro (show weightCoeff 7 3 * weightCoeff 7 1 + 155 =
    weightCoeff 7 2 * weightCoeff 7 2 from rfl)

theorem toeplitz_two_seven_two : toeplitzTwoMinorNonnegative 7 2 :=
  Nat.le.intro (show weightCoeff 7 4 * weightCoeff 7 2 + 85 =
    weightCoeff 7 3 * weightCoeff 7 3 from rfl)

theorem toeplitz_two_seven_three : toeplitzTwoMinorNonnegative 7 3 :=
  Nat.le.intro (show weightCoeff 7 5 * weightCoeff 7 3 + 1 =
    weightCoeff 7 4 * weightCoeff 7 4 from rfl)

theorem toeplitz_two_eight_zero : toeplitzTwoMinorNonnegative 8 0 :=
  Nat.le.intro (show weightCoeff 8 2 * weightCoeff 8 0 + 43 =
    weightCoeff 8 1 * weightCoeff 8 1 from rfl)

theorem toeplitz_two_eight_one : toeplitzTwoMinorNonnegative 8 1 :=
  Nat.le.intro (show weightCoeff 8 3 * weightCoeff 8 1 + 281 =
    weightCoeff 8 2 * weightCoeff 8 2 from rfl)

theorem toeplitz_two_eight_two : toeplitzTwoMinorNonnegative 8 2 :=
  Nat.le.intro (show weightCoeff 8 4 * weightCoeff 8 2 + 295 =
    weightCoeff 8 3 * weightCoeff 8 3 from rfl)

theorem toeplitz_two_eight_three : toeplitzTwoMinorNonnegative 8 3 :=
  Nat.le.intro (show weightCoeff 8 5 * weightCoeff 8 3 + 25 =
    weightCoeff 8 4 * weightCoeff 8 4 from rfl)

theorem toeplitz_two_nine_zero : toeplitzTwoMinorNonnegative 9 0 :=
  Nat.le.intro (show weightCoeff 9 2 * weightCoeff 9 0 + 53 =
    weightCoeff 9 1 * weightCoeff 9 1 from rfl)

theorem toeplitz_two_nine_one : toeplitzTwoMinorNonnegative 9 1 :=
  Nat.le.intro (show weightCoeff 9 3 * weightCoeff 9 1 + 469 =
    weightCoeff 9 2 * weightCoeff 9 2 from rfl)

theorem toeplitz_two_nine_two : toeplitzTwoMinorNonnegative 9 2 :=
  Nat.le.intro (show weightCoeff 9 4 * weightCoeff 9 2 + 805 =
    weightCoeff 9 3 * weightCoeff 9 3 from rfl)

theorem toeplitz_two_nine_three : toeplitzTwoMinorNonnegative 9 3 :=
  Nat.le.intro (show weightCoeff 9 5 * weightCoeff 9 3 + 190 =
    weightCoeff 9 4 * weightCoeff 9 4 from rfl)

theorem toeplitz_two_nine_four : toeplitzTwoMinorNonnegative 9 4 :=
  Nat.le.intro (show weightCoeff 9 6 * weightCoeff 9 4 + 1 =
    weightCoeff 9 5 * weightCoeff 9 5 from rfl)

theorem toeplitz_two_ten_zero : toeplitzTwoMinorNonnegative 10 0 :=
  Nat.le.intro (show weightCoeff 10 2 * weightCoeff 10 0 + 64 =
    weightCoeff 10 1 * weightCoeff 10 1 from rfl)

theorem toeplitz_two_ten_one : toeplitzTwoMinorNonnegative 10 1 :=
  Nat.le.intro (show weightCoeff 10 3 * weightCoeff 10 1 + 736 =
    weightCoeff 10 2 * weightCoeff 10 2 from rfl)

theorem toeplitz_two_ten_two : toeplitzTwoMinorNonnegative 10 2 :=
  Nat.le.intro (show weightCoeff 10 4 * weightCoeff 10 2 + 1876 =
    weightCoeff 10 3 * weightCoeff 10 3 from rfl)

theorem toeplitz_two_ten_three : toeplitzTwoMinorNonnegative 10 3 :=
  Nat.le.intro (show weightCoeff 10 5 * weightCoeff 10 3 + 889 =
    weightCoeff 10 4 * weightCoeff 10 4 from rfl)

theorem toeplitz_two_ten_four : toeplitzTwoMinorNonnegative 10 4 :=
  Nat.le.intro (show weightCoeff 10 6 * weightCoeff 10 4 + 36 =
    weightCoeff 10 5 * weightCoeff 10 5 from rfl)

theorem toeplitz_three_six_zero : toeplitzThreeMinorNonnegative 6 0 :=
  Nat.le.intro (show toeplitzThreeNegative 6 0 + 536 =
    toeplitzThreePositive 6 0 from rfl)

theorem toeplitz_three_six_one : toeplitzThreeMinorNonnegative 6 1 :=
  Nat.le.intro (show toeplitzThreeNegative 6 1 + 64 =
    toeplitzThreePositive 6 1 from rfl)

theorem toeplitz_three_seven_zero : toeplitzThreeMinorNonnegative 7 0 :=
  Nat.le.intro (show toeplitzThreeNegative 7 0 + 1409 =
    toeplitzThreePositive 7 0 from rfl)

theorem toeplitz_three_seven_one : toeplitzThreeMinorNonnegative 7 1 :=
  Nat.le.intro (show toeplitzThreeNegative 7 1 + 707 =
    toeplitzThreePositive 7 1 from rfl)

theorem toeplitz_three_seven_two : toeplitzThreeMinorNonnegative 7 2 :=
  Nat.le.intro (show toeplitzThreeNegative 7 2 + 1 =
    toeplitzThreePositive 7 2 from rfl)

theorem toeplitz_three_eight_zero : toeplitzThreeMinorNonnegative 8 0 :=
  Nat.le.intro (show toeplitzThreeNegative 8 0 + 3156 =
    toeplitzThreePositive 8 0 from rfl)

theorem toeplitz_three_eight_one : toeplitzThreeMinorNonnegative 8 1 :=
  Nat.le.intro (show toeplitzThreeNegative 8 1 + 4000 =
    toeplitzThreePositive 8 1 from rfl)

theorem toeplitz_three_eight_two : toeplitzThreeMinorNonnegative 8 2 :=
  Nat.le.intro (show toeplitzThreeNegative 8 2 + 125 =
    toeplitzThreePositive 8 2 from rfl)

theorem toeplitz_three_nine_zero : toeplitzThreeMinorNonnegative 9 0 :=
  Nat.le.intro (show toeplitzThreeNegative 9 0 + 6332 =
    toeplitzThreePositive 9 0 from rfl)

theorem toeplitz_three_nine_one : toeplitzThreeMinorNonnegative 9 1 :=
  Nat.le.intro (show toeplitzThreeNegative 9 1 + 15969 =
    toeplitzThreePositive 9 1 from rfl)

theorem toeplitz_three_nine_two : toeplitzThreeMinorNonnegative 9 2 :=
  Nat.le.intro (show toeplitzThreeNegative 9 2 + 2353 =
    toeplitzThreePositive 9 2 from rfl)

theorem toeplitz_three_nine_three : toeplitzThreeMinorNonnegative 9 3 :=
  Nat.le.intro (show toeplitzThreeNegative 9 3 + 1 =
    toeplitzThreePositive 9 3 from rfl)

theorem toeplitz_three_ten_zero : toeplitzThreeMinorNonnegative 10 0 :=
  Nat.le.intro (show toeplitzThreeNegative 10 0 + 11712 =
    toeplitzThreePositive 10 0 from rfl)

theorem toeplitz_three_ten_one : toeplitzThreeMinorNonnegative 10 1 :=
  Nat.le.intro (show toeplitzThreeNegative 10 1 + 51162 =
    toeplitzThreePositive 10 1 from rfl)

theorem toeplitz_three_ten_two : toeplitzThreeMinorNonnegative 10 2 :=
  Nat.le.intro (show toeplitzThreeNegative 10 2 + 20651 =
    toeplitzThreePositive 10 2 from rfl)

theorem toeplitz_three_ten_three : toeplitzThreeMinorNonnegative 10 3 :=
  Nat.le.intro (show toeplitzThreeNegative 10 3 + 216 =
    toeplitzThreePositive 10 3 from rfl)

theorem window_six_to_ten_weight_toeplitz_two_total_positive :
    toeplitzTwoMinorNonnegative 6 0 /\
    toeplitzTwoMinorNonnegative 6 1 /\
    toeplitzTwoMinorNonnegative 6 2 /\
    toeplitzTwoMinorNonnegative 7 0 /\
    toeplitzTwoMinorNonnegative 7 1 /\
    toeplitzTwoMinorNonnegative 7 2 /\
    toeplitzTwoMinorNonnegative 7 3 /\
    toeplitzTwoMinorNonnegative 8 0 /\
    toeplitzTwoMinorNonnegative 8 1 /\
    toeplitzTwoMinorNonnegative 8 2 /\
    toeplitzTwoMinorNonnegative 8 3 /\
    toeplitzTwoMinorNonnegative 9 0 /\
    toeplitzTwoMinorNonnegative 9 1 /\
    toeplitzTwoMinorNonnegative 9 2 /\
    toeplitzTwoMinorNonnegative 9 3 /\
    toeplitzTwoMinorNonnegative 9 4 /\
    toeplitzTwoMinorNonnegative 10 0 /\
    toeplitzTwoMinorNonnegative 10 1 /\
    toeplitzTwoMinorNonnegative 10 2 /\
    toeplitzTwoMinorNonnegative 10 3 /\
    toeplitzTwoMinorNonnegative 10 4 := by
  constructor
  exact toeplitz_two_six_zero
  constructor
  exact toeplitz_two_six_one
  constructor
  exact toeplitz_two_six_two
  constructor
  exact toeplitz_two_seven_zero
  constructor
  exact toeplitz_two_seven_one
  constructor
  exact toeplitz_two_seven_two
  constructor
  exact toeplitz_two_seven_three
  constructor
  exact toeplitz_two_eight_zero
  constructor
  exact toeplitz_two_eight_one
  constructor
  exact toeplitz_two_eight_two
  constructor
  exact toeplitz_two_eight_three
  constructor
  exact toeplitz_two_nine_zero
  constructor
  exact toeplitz_two_nine_one
  constructor
  exact toeplitz_two_nine_two
  constructor
  exact toeplitz_two_nine_three
  constructor
  exact toeplitz_two_nine_four
  constructor
  exact toeplitz_two_ten_zero
  constructor
  exact toeplitz_two_ten_one
  constructor
  exact toeplitz_two_ten_two
  constructor
  exact toeplitz_two_ten_three
  exact toeplitz_two_ten_four

theorem window_six_to_ten_weight_toeplitz_three_total_positive :
    toeplitzThreeMinorNonnegative 6 0 /\
    toeplitzThreeMinorNonnegative 6 1 /\
    toeplitzThreeMinorNonnegative 7 0 /\
    toeplitzThreeMinorNonnegative 7 1 /\
    toeplitzThreeMinorNonnegative 7 2 /\
    toeplitzThreeMinorNonnegative 8 0 /\
    toeplitzThreeMinorNonnegative 8 1 /\
    toeplitzThreeMinorNonnegative 8 2 /\
    toeplitzThreeMinorNonnegative 9 0 /\
    toeplitzThreeMinorNonnegative 9 1 /\
    toeplitzThreeMinorNonnegative 9 2 /\
    toeplitzThreeMinorNonnegative 9 3 /\
    toeplitzThreeMinorNonnegative 10 0 /\
    toeplitzThreeMinorNonnegative 10 1 /\
    toeplitzThreeMinorNonnegative 10 2 /\
    toeplitzThreeMinorNonnegative 10 3 := by
  constructor
  exact toeplitz_three_six_zero
  constructor
  exact toeplitz_three_six_one
  constructor
  exact toeplitz_three_seven_zero
  constructor
  exact toeplitz_three_seven_one
  constructor
  exact toeplitz_three_seven_two
  constructor
  exact toeplitz_three_eight_zero
  constructor
  exact toeplitz_three_eight_one
  constructor
  exact toeplitz_three_eight_two
  constructor
  exact toeplitz_three_nine_zero
  constructor
  exact toeplitz_three_nine_one
  constructor
  exact toeplitz_three_nine_two
  constructor
  exact toeplitz_three_nine_three
  constructor
  exact toeplitz_three_ten_zero
  constructor
  exact toeplitz_three_ten_one
  constructor
  exact toeplitz_three_ten_two
  exact toeplitz_three_ten_three

def windowSixToTenWeightToeplitzTotalPositive : Prop :=
  (toeplitzTwoMinorNonnegative 6 0 /\
    toeplitzTwoMinorNonnegative 6 1 /\
    toeplitzTwoMinorNonnegative 6 2 /\
    toeplitzTwoMinorNonnegative 7 0 /\
    toeplitzTwoMinorNonnegative 7 1 /\
    toeplitzTwoMinorNonnegative 7 2 /\
    toeplitzTwoMinorNonnegative 7 3 /\
    toeplitzTwoMinorNonnegative 8 0 /\
    toeplitzTwoMinorNonnegative 8 1 /\
    toeplitzTwoMinorNonnegative 8 2 /\
    toeplitzTwoMinorNonnegative 8 3 /\
    toeplitzTwoMinorNonnegative 9 0 /\
    toeplitzTwoMinorNonnegative 9 1 /\
    toeplitzTwoMinorNonnegative 9 2 /\
    toeplitzTwoMinorNonnegative 9 3 /\
    toeplitzTwoMinorNonnegative 9 4 /\
    toeplitzTwoMinorNonnegative 10 0 /\
    toeplitzTwoMinorNonnegative 10 1 /\
    toeplitzTwoMinorNonnegative 10 2 /\
    toeplitzTwoMinorNonnegative 10 3 /\
    toeplitzTwoMinorNonnegative 10 4) /\
  (toeplitzThreeMinorNonnegative 6 0 /\
    toeplitzThreeMinorNonnegative 6 1 /\
    toeplitzThreeMinorNonnegative 7 0 /\
    toeplitzThreeMinorNonnegative 7 1 /\
    toeplitzThreeMinorNonnegative 7 2 /\
    toeplitzThreeMinorNonnegative 8 0 /\
    toeplitzThreeMinorNonnegative 8 1 /\
    toeplitzThreeMinorNonnegative 8 2 /\
    toeplitzThreeMinorNonnegative 9 0 /\
    toeplitzThreeMinorNonnegative 9 1 /\
    toeplitzThreeMinorNonnegative 9 2 /\
    toeplitzThreeMinorNonnegative 9 3 /\
    toeplitzThreeMinorNonnegative 10 0 /\
    toeplitzThreeMinorNonnegative 10 1 /\
    toeplitzThreeMinorNonnegative 10 2 /\
    toeplitzThreeMinorNonnegative 10 3)

theorem window_six_to_ten_weight_toeplitz_total_positive_certificate :
    windowSixToTenWeightToeplitzTotalPositive := by
  unfold windowSixToTenWeightToeplitzTotalPositive
  constructor
  exact window_six_to_ten_weight_toeplitz_two_total_positive
  exact window_six_to_ten_weight_toeplitz_three_total_positive

end Window6WeightToeplitzTotalPositive
end Derived
end BEDC
