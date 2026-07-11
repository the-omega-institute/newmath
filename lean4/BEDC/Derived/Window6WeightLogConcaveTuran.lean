namespace BEDC
namespace Derived
namespace Window6WeightLogConcaveTuran

set_option maxRecDepth 10000

/-!
Fibonacci-cube weight-polynomial coefficients give a finite carrier for
degree-two Turan positivity.  The certificates below prove concrete
log-concavity inequalities for the finite windows `m = 6, 7, 8, 9, 10`.
They model the degree-two Jensen/Laguerre-Polya shape on this carrier; they
are not a proof of RH.
-/

def listAppend {α : Type} : List α -> List α -> List α
  | [], ys => ys
  | x :: xs, ys => x :: listAppend xs ys

def listMap {α β : Type} (f : α -> β) : List α -> List β
  | [] => []
  | x :: xs => f x :: listMap f xs

def boolWords : Nat -> List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      let ws := boolWords n
      listAppend (listMap (fun w => false :: w) ws)
        (listMap (fun w => true :: w) ws)

def noAdj : List Bool -> Bool
  | [] => true
  | b :: rest =>
      match rest with
      | [] => true
      | c :: _ =>
          match b with
          | true =>
              match c with
              | true => false
              | false => noAdj rest
          | false => noAdj rest

def trueCount : List Bool -> Nat
  | [] => 0
  | false :: rest => trueCount rest
  | true :: rest => trueCount rest + 1

def natEqBool : Nat -> Nat -> Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | a + 1, b + 1 => natEqBool a b

def weightCoeffFromWords (k : Nat) : List (List Bool) -> Nat
  | [] => 0
  | w :: rest =>
      match noAdj w with
      | true =>
        match natEqBool (trueCount w) k with
        | true =>
          weightCoeffFromWords k rest + 1
        | false =>
          weightCoeffFromWords k rest
      | false =>
        weightCoeffFromWords k rest

def weightCoeff (m k : Nat) : Nat :=
  weightCoeffFromWords k (boolWords m)

def turanAt (m k : Nat) : Prop :=
  weightCoeff m (k + 1) * weightCoeff m (k - 1) <=
    weightCoeff m k * weightCoeff m k

theorem weightCoeff_six_zero : weightCoeff 6 0 = 1 := rfl

theorem weightCoeff_six_one : weightCoeff 6 1 = 6 := rfl

theorem weightCoeff_six_two : weightCoeff 6 2 = 10 := rfl

theorem weightCoeff_six_three : weightCoeff 6 3 = 4 := rfl

theorem weightCoeff_six_total : weightCoeff 6 0 + weightCoeff 6 1 +
    weightCoeff 6 2 + weightCoeff 6 3 = 21 := rfl

theorem turan_six_one : turanAt 6 1 :=
  Nat.le.intro (show weightCoeff 6 2 * weightCoeff 6 0 + 26 =
    weightCoeff 6 1 * weightCoeff 6 1 from rfl)

theorem turan_six_two : turanAt 6 2 :=
  Nat.le.intro (show weightCoeff 6 3 * weightCoeff 6 1 + 76 =
    weightCoeff 6 2 * weightCoeff 6 2 from rfl)

theorem turan_seven_one : turanAt 7 1 :=
  Nat.le.intro (show weightCoeff 7 2 * weightCoeff 7 0 + 34 =
    weightCoeff 7 1 * weightCoeff 7 1 from rfl)

theorem turan_seven_two : turanAt 7 2 :=
  Nat.le.intro (show weightCoeff 7 3 * weightCoeff 7 1 + 155 =
    weightCoeff 7 2 * weightCoeff 7 2 from rfl)

theorem turan_seven_three : turanAt 7 3 :=
  Nat.le.intro (show weightCoeff 7 4 * weightCoeff 7 2 + 85 =
    weightCoeff 7 3 * weightCoeff 7 3 from rfl)

theorem turan_eight_one : turanAt 8 1 :=
  Nat.le.intro (show weightCoeff 8 2 * weightCoeff 8 0 + 43 =
    weightCoeff 8 1 * weightCoeff 8 1 from rfl)

theorem turan_eight_two : turanAt 8 2 :=
  Nat.le.intro (show weightCoeff 8 3 * weightCoeff 8 1 + 281 =
    weightCoeff 8 2 * weightCoeff 8 2 from rfl)

theorem turan_eight_three : turanAt 8 3 :=
  Nat.le.intro (show weightCoeff 8 4 * weightCoeff 8 2 + 295 =
    weightCoeff 8 3 * weightCoeff 8 3 from rfl)

theorem turan_nine_one : turanAt 9 1 :=
  Nat.le.intro (show weightCoeff 9 2 * weightCoeff 9 0 + 53 =
    weightCoeff 9 1 * weightCoeff 9 1 from rfl)

theorem turan_nine_two : turanAt 9 2 :=
  Nat.le.intro (show weightCoeff 9 3 * weightCoeff 9 1 + 469 =
    weightCoeff 9 2 * weightCoeff 9 2 from rfl)

theorem turan_nine_three : turanAt 9 3 :=
  Nat.le.intro (show weightCoeff 9 4 * weightCoeff 9 2 + 805 =
    weightCoeff 9 3 * weightCoeff 9 3 from rfl)

theorem turan_nine_four : turanAt 9 4 :=
  Nat.le.intro (show weightCoeff 9 5 * weightCoeff 9 3 + 190 =
    weightCoeff 9 4 * weightCoeff 9 4 from rfl)

theorem turan_ten_one : turanAt 10 1 :=
  Nat.le.intro (show weightCoeff 10 2 * weightCoeff 10 0 + 64 =
    weightCoeff 10 1 * weightCoeff 10 1 from rfl)

theorem turan_ten_two : turanAt 10 2 :=
  Nat.le.intro (show weightCoeff 10 3 * weightCoeff 10 1 + 736 =
    weightCoeff 10 2 * weightCoeff 10 2 from rfl)

theorem turan_ten_three : turanAt 10 3 :=
  Nat.le.intro (show weightCoeff 10 4 * weightCoeff 10 2 + 1876 =
    weightCoeff 10 3 * weightCoeff 10 3 from rfl)

theorem turan_ten_four : turanAt 10 4 :=
  Nat.le.intro (show weightCoeff 10 5 * weightCoeff 10 3 + 889 =
    weightCoeff 10 4 * weightCoeff 10 4 from rfl)

theorem window_six_to_ten_weight_logconcave_turan :
    turanAt 6 1 ∧ turanAt 6 2 ∧
    turanAt 7 1 ∧ turanAt 7 2 ∧ turanAt 7 3 ∧
    turanAt 8 1 ∧ turanAt 8 2 ∧ turanAt 8 3 ∧
    turanAt 9 1 ∧ turanAt 9 2 ∧ turanAt 9 3 ∧ turanAt 9 4 ∧
    turanAt 10 1 ∧ turanAt 10 2 ∧ turanAt 10 3 ∧ turanAt 10 4 := by
  constructor
  exact turan_six_one
  constructor
  exact turan_six_two
  constructor
  exact turan_seven_one
  constructor
  exact turan_seven_two
  constructor
  exact turan_seven_three
  constructor
  exact turan_eight_one
  constructor
  exact turan_eight_two
  constructor
  exact turan_eight_three
  constructor
  exact turan_nine_one
  constructor
  exact turan_nine_two
  constructor
  exact turan_nine_three
  constructor
  exact turan_nine_four
  constructor
  exact turan_ten_one
  constructor
  exact turan_ten_two
  constructor
  exact turan_ten_three
  exact turan_ten_four

end Window6WeightLogConcaveTuran
end Derived
end BEDC
