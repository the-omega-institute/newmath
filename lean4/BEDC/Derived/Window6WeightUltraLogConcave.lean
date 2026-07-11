import BEDC.Derived.Window6WeightLogConcaveTuran

namespace BEDC
namespace Derived
namespace Window6WeightUltraLogConcave

set_option maxRecDepth 10000

/-!
Newton inequality is the coefficient-side necessary strengthening forced by
real-rootedness.  It refines log-concavity as finite-window positivity on the
Jensen/Laguerre-Polya ladder, here as a finite certificate on the Fibonacci
carrier.  It is not an RH proof.
-/

open Window6WeightLogConcaveTuran (weightCoeff)

def weightDegree (m : Nat) : Nat :=
  (m + 1) / 2

def newtonAt (m k : Nat) : Prop :=
  weightCoeff m (k - 1) * weightCoeff m (k + 1) *
      (k + 1) * (weightDegree m - k + 1) <=
    weightCoeff m k * weightCoeff m k * k * (weightDegree m - k)

theorem weight_degree_six : weightDegree 6 = 3 := rfl

theorem weight_degree_seven : weightDegree 7 = 4 := rfl

theorem weight_degree_eight : weightDegree 8 = 4 := rfl

theorem weight_degree_nine : weightDegree 9 = 5 := rfl

theorem weight_degree_ten : weightDegree 10 = 5 := rfl

theorem weightCoeff_six_zero : weightCoeff 6 0 = 1 := rfl

theorem weightCoeff_six_one : weightCoeff 6 1 = 6 := rfl

theorem weightCoeff_six_two : weightCoeff 6 2 = 10 := rfl

theorem weightCoeff_six_three : weightCoeff 6 3 = 4 := rfl

theorem weightCoeff_seven_zero : weightCoeff 7 0 = 1 := rfl

theorem weightCoeff_seven_one : weightCoeff 7 1 = 7 := rfl

theorem weightCoeff_seven_two : weightCoeff 7 2 = 15 := rfl

theorem weightCoeff_seven_three : weightCoeff 7 3 = 10 := rfl

theorem weightCoeff_seven_four : weightCoeff 7 4 = 1 := rfl

theorem weightCoeff_eight_zero : weightCoeff 8 0 = 1 := rfl

theorem weightCoeff_eight_one : weightCoeff 8 1 = 8 := rfl

theorem weightCoeff_eight_two : weightCoeff 8 2 = 21 := rfl

theorem weightCoeff_eight_three : weightCoeff 8 3 = 20 := rfl

theorem weightCoeff_eight_four : weightCoeff 8 4 = 5 := rfl

theorem weightCoeff_nine_zero : weightCoeff 9 0 = 1 := rfl

theorem weightCoeff_nine_one : weightCoeff 9 1 = 9 := rfl

theorem weightCoeff_nine_two : weightCoeff 9 2 = 28 := rfl

theorem weightCoeff_nine_three : weightCoeff 9 3 = 35 := rfl

theorem weightCoeff_nine_four : weightCoeff 9 4 = 15 := rfl

theorem weightCoeff_nine_five : weightCoeff 9 5 = 1 := rfl

theorem weightCoeff_ten_zero : weightCoeff 10 0 = 1 := rfl

theorem weightCoeff_ten_one : weightCoeff 10 1 = 10 := rfl

theorem weightCoeff_ten_two : weightCoeff 10 2 = 36 := rfl

theorem weightCoeff_ten_three : weightCoeff 10 3 = 56 := rfl

theorem weightCoeff_ten_four : weightCoeff 10 4 = 35 := rfl

theorem weightCoeff_ten_five : weightCoeff 10 5 = 6 := rfl

theorem newton_six_one : newtonAt 6 1 :=
  Nat.le.intro (show
    weightCoeff 6 (1 - 1) * weightCoeff 6 (1 + 1) *
        (1 + 1) * (weightDegree 6 - 1 + 1) + 12 =
      weightCoeff 6 1 * weightCoeff 6 1 * 1 * (weightDegree 6 - 1) from rfl)

theorem newton_six_two : newtonAt 6 2 :=
  Nat.le.intro (show
    weightCoeff 6 (2 - 1) * weightCoeff 6 (2 + 1) *
        (2 + 1) * (weightDegree 6 - 2 + 1) + 56 =
      weightCoeff 6 2 * weightCoeff 6 2 * 2 * (weightDegree 6 - 2) from rfl)

theorem newton_seven_one : newtonAt 7 1 :=
  Nat.le.intro (show
    weightCoeff 7 (1 - 1) * weightCoeff 7 (1 + 1) *
        (1 + 1) * (weightDegree 7 - 1 + 1) + 27 =
      weightCoeff 7 1 * weightCoeff 7 1 * 1 * (weightDegree 7 - 1) from rfl)

theorem newton_seven_two : newtonAt 7 2 :=
  Nat.le.intro (show
    weightCoeff 7 (2 - 1) * weightCoeff 7 (2 + 1) *
        (2 + 1) * (weightDegree 7 - 2 + 1) + 270 =
      weightCoeff 7 2 * weightCoeff 7 2 * 2 * (weightDegree 7 - 2) from rfl)

theorem newton_seven_three : newtonAt 7 3 :=
  Nat.le.intro (show
    weightCoeff 7 (3 - 1) * weightCoeff 7 (3 + 1) *
        (3 + 1) * (weightDegree 7 - 3 + 1) + 180 =
      weightCoeff 7 3 * weightCoeff 7 3 * 3 * (weightDegree 7 - 3) from rfl)

theorem newton_eight_one : newtonAt 8 1 :=
  Nat.le.intro (show
    weightCoeff 8 (1 - 1) * weightCoeff 8 (1 + 1) *
        (1 + 1) * (weightDegree 8 - 1 + 1) + 24 =
      weightCoeff 8 1 * weightCoeff 8 1 * 1 * (weightDegree 8 - 1) from rfl)

theorem newton_eight_two : newtonAt 8 2 :=
  Nat.le.intro (show
    weightCoeff 8 (2 - 1) * weightCoeff 8 (2 + 1) *
        (2 + 1) * (weightDegree 8 - 2 + 1) + 324 =
      weightCoeff 8 2 * weightCoeff 8 2 * 2 * (weightDegree 8 - 2) from rfl)

theorem newton_eight_three : newtonAt 8 3 :=
  Nat.le.intro (show
    weightCoeff 8 (3 - 1) * weightCoeff 8 (3 + 1) *
        (3 + 1) * (weightDegree 8 - 3 + 1) + 360 =
      weightCoeff 8 3 * weightCoeff 8 3 * 3 * (weightDegree 8 - 3) from rfl)

theorem newton_nine_one : newtonAt 9 1 :=
  Nat.le.intro (show
    weightCoeff 9 (1 - 1) * weightCoeff 9 (1 + 1) *
        (1 + 1) * (weightDegree 9 - 1 + 1) + 44 =
      weightCoeff 9 1 * weightCoeff 9 1 * 1 * (weightDegree 9 - 1) from rfl)

theorem newton_nine_two : newtonAt 9 2 :=
  Nat.le.intro (show
    weightCoeff 9 (2 - 1) * weightCoeff 9 (2 + 1) *
        (2 + 1) * (weightDegree 9 - 2 + 1) + 924 =
      weightCoeff 9 2 * weightCoeff 9 2 * 2 * (weightDegree 9 - 2) from rfl)

theorem newton_nine_three : newtonAt 9 3 :=
  Nat.le.intro (show
    weightCoeff 9 (3 - 1) * weightCoeff 9 (3 + 1) *
        (3 + 1) * (weightDegree 9 - 3 + 1) + 2310 =
      weightCoeff 9 3 * weightCoeff 9 3 * 3 * (weightDegree 9 - 3) from rfl)

theorem newton_nine_four : newtonAt 9 4 :=
  Nat.le.intro (show
    weightCoeff 9 (4 - 1) * weightCoeff 9 (4 + 1) *
        (4 + 1) * (weightDegree 9 - 4 + 1) + 550 =
      weightCoeff 9 4 * weightCoeff 9 4 * 4 * (weightDegree 9 - 4) from rfl)

theorem newton_ten_one : newtonAt 10 1 :=
  Nat.le.intro (show
    weightCoeff 10 (1 - 1) * weightCoeff 10 (1 + 1) *
        (1 + 1) * (weightDegree 10 - 1 + 1) + 40 =
      weightCoeff 10 1 * weightCoeff 10 1 * 1 * (weightDegree 10 - 1) from rfl)

theorem newton_ten_two : newtonAt 10 2 :=
  Nat.le.intro (show
    weightCoeff 10 (2 - 1) * weightCoeff 10 (2 + 1) *
        (2 + 1) * (weightDegree 10 - 2 + 1) + 1056 =
      weightCoeff 10 2 * weightCoeff 10 2 * 2 * (weightDegree 10 - 2) from rfl)

theorem newton_ten_three : newtonAt 10 3 :=
  Nat.le.intro (show
    weightCoeff 10 (3 - 1) * weightCoeff 10 (3 + 1) *
        (3 + 1) * (weightDegree 10 - 3 + 1) + 3696 =
      weightCoeff 10 3 * weightCoeff 10 3 * 3 * (weightDegree 10 - 3) from rfl)

theorem newton_ten_four : newtonAt 10 4 :=
  Nat.le.intro (show
    weightCoeff 10 (4 - 1) * weightCoeff 10 (4 + 1) *
        (4 + 1) * (weightDegree 10 - 4 + 1) + 1540 =
      weightCoeff 10 4 * weightCoeff 10 4 * 4 * (weightDegree 10 - 4) from rfl)

theorem window_six_to_ten_weight_newton_ultra_log_concave :
    newtonAt 6 1 ∧ newtonAt 6 2 ∧
    newtonAt 7 1 ∧ newtonAt 7 2 ∧ newtonAt 7 3 ∧
    newtonAt 8 1 ∧ newtonAt 8 2 ∧ newtonAt 8 3 ∧
    newtonAt 9 1 ∧ newtonAt 9 2 ∧ newtonAt 9 3 ∧ newtonAt 9 4 ∧
    newtonAt 10 1 ∧ newtonAt 10 2 ∧ newtonAt 10 3 ∧ newtonAt 10 4 := by
  constructor
  exact newton_six_one
  constructor
  exact newton_six_two
  constructor
  exact newton_seven_one
  constructor
  exact newton_seven_two
  constructor
  exact newton_seven_three
  constructor
  exact newton_eight_one
  constructor
  exact newton_eight_two
  constructor
  exact newton_eight_three
  constructor
  exact newton_nine_one
  constructor
  exact newton_nine_two
  constructor
  exact newton_nine_three
  constructor
  exact newton_nine_four
  constructor
  exact newton_ten_one
  constructor
  exact newton_ten_two
  constructor
  exact newton_ten_three
  exact newton_ten_four

end Window6WeightUltraLogConcave
end Derived
end BEDC
