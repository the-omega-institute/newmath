import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.IntUp.CommRing

namespace BEDC.Derived.PochhammerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def intOfNatUp (n : BHist) (hn : UnaryHistory n) : Z :=
  BEDC.Derived.RationalUp.intOfNat n hn

def intOfNatStd (n : Nat) : Z :=
  intOfNatUp (natToUnary n) (natToUnary_unary n)

def descPochhammerInt (x : Z) : Nat -> Z
  | 0 => integerRing.one
  | Nat.succ n =>
      integerRing.mul (descPochhammerInt x n)
        (integerRing.sub x (intOfNatStd n))

def ascPochhammerInt (x : Z) : Nat -> Z
  | 0 => integerRing.one
  | Nat.succ n =>
      integerRing.mul (ascPochhammerInt x n)
        (integerRing.add x (intOfNatStd n))

theorem descPochhammerInt_zero (x : Z) :
    Zeq (descPochhammerInt x 0) integerRing.one := by
  exact integerRing.refl integerRing.one

theorem ascPochhammerInt_zero (x : Z) :
    Zeq (ascPochhammerInt x 0) integerRing.one := by
  exact integerRing.refl integerRing.one

theorem descPochhammerInt_succ (x : Z) (n : Nat) :
    Zeq (descPochhammerInt x (Nat.succ n))
      (integerRing.mul (descPochhammerInt x n)
        (integerRing.sub x (intOfNatStd n))) := by
  exact integerRing.refl (descPochhammerInt x (Nat.succ n))

theorem ascPochhammerInt_succ (x : Z) (n : Nat) :
    Zeq (ascPochhammerInt x (Nat.succ n))
      (integerRing.mul (ascPochhammerInt x n)
        (integerRing.add x (intOfNatStd n))) := by
  exact integerRing.refl (ascPochhammerInt x (Nat.succ n))

theorem descPochhammerInt_one (x : Z) :
    Zeq (descPochhammerInt x 1) x := by
  exact integerRing.trans
    (integerRing.mul_congr (integerRing.refl integerRing.one)
      (integerRing.trans (integerRing.sub_eq_add_neg x integerRing.zero)
        (integerRing.trans
          (integerRing.add_congr (integerRing.refl x)
            integerRing.neg_zero)
          (integerRing.add_zero x))))
    (integerRing.one_mul x)

theorem ascPochhammerInt_one (x : Z) :
    Zeq (ascPochhammerInt x 1) x := by
  exact integerRing.trans
    (integerRing.mul_congr (integerRing.refl integerRing.one)
      (integerRing.add_zero x))
    (integerRing.one_mul x)

private def natDescAux : Nat -> Nat -> Nat
  | _, 0 => 1
  | x, Nat.succ k => natDescAux x k * (x - k)

def natDescPochhammerCount (n k : Nat) : Nat :=
  natDescAux n k

def natDescPochhammerFn (n k : BHist) : BHist :=
  natToUnary (natDescPochhammerCount (bwordLength n) (bwordLength k))

theorem natDescPochhammerFn_unary (n k : BHist) :
    UnaryHistory (natDescPochhammerFn n k) := by
  unfold natDescPochhammerFn
  exact natToUnary_unary _

theorem natDescPochhammerCount_zero_right (n : Nat) :
    natDescPochhammerCount n 0 = 1 := by
  rfl

theorem natDescPochhammerCount_succ (n k : Nat) :
    natDescPochhammerCount n (Nat.succ k) =
      natDescPochhammerCount n k * (n - k) := by
  rfl

def natFactorialCount (n : Nat) : Nat :=
  bwordLength (natFactorialFn (natToUnary n))

def natChooseCount (n k : Nat) : Nat :=
  bwordLength (natChooseFn (natToUnary n) (natToUnary k))

theorem natFactorialCount_zero :
    natFactorialCount 0 = 1 := by
  rfl

theorem natChooseCount_zero_right (n : Nat) :
    natChooseCount n 0 = 1 := by
  unfold natChooseCount natChooseFn
  rw [natToUnary_length]
  cases n <;> rfl

theorem natChooseCount_pascal (n k : Nat) :
    natChooseCount (Nat.succ n) (Nat.succ k) =
      natChooseCount n k + natChooseCount n (Nat.succ k) := by
  unfold natChooseCount natChooseFn
  repeat rw [natToUnary_length]
  rfl

theorem natDescPochhammerFn_zero_right (n : BHist) :
    natDescPochhammerFn n BHist.Empty = NatOne := by
  unfold natDescPochhammerFn
  rfl

private theorem natDescAux_zero_left :
    ∀ k : Nat, natDescAux 0 (Nat.succ k) = 0 := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      unfold natDescAux
      rw [ih]
      exact Nat.zero_mul _

theorem natDescPochhammerCount_zero_left_succ (k : Nat) :
    natDescPochhammerCount 0 (Nat.succ k) = 0 :=
  natDescAux_zero_left k

theorem natDescPochhammerFn_zero_left_succ (k : Nat) :
    natDescPochhammerFn BHist.Empty (natToUnary (Nat.succ k)) = BHist.Empty := by
  unfold natDescPochhammerFn
  rw [natToUnary_length]
  change natToUnary (natDescPochhammerCount 0 (Nat.succ k)) = BHist.Empty
  rw [natDescPochhammerCount_zero_left_succ]
  rfl

private theorem nat_mul_assoc_clean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

private theorem nat_add_mul_clean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      calc
        (a + b) * Nat.succ c =
            (a + b) * c + (a + b) := Nat.mul_succ (a + b) c
        _ = (a * c + b * c) + (a + b) :=
          congrArg (fun x => x + (a + b)) ih
        _ = a * c + (b * c + (a + b)) :=
          Nat.add_assoc (a * c) (b * c) (a + b)
        _ = a * c + ((b * c + a) + b) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc (b * c) a b).symm
        _ = a * c + ((a + b * c) + b) :=
          congrArg (fun x => a * c + (x + b)) (Nat.add_comm (b * c) a)
        _ = a * c + (a + (b * c + b)) :=
          congrArg (fun x => a * c + x) (Nat.add_assoc a (b * c) b)
        _ = (a * c + a) + (b * c + b) :=
          (Nat.add_assoc (a * c) a (b * c + b)).symm
        _ = a * Nat.succ c + (b * c + b) :=
          congrArg (fun x => x + (b * c + b)) (Nat.mul_succ a c).symm
        _ = a * Nat.succ c + b * Nat.succ c :=
          congrArg (fun x => a * Nat.succ c + x) (Nat.mul_succ b c).symm

private theorem nat_sub_zero_clean (n : Nat) : n - 0 = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rfl

private theorem nat_sub_add_eq_clean (a b c : Nat) :
    a - (b + c) = a - b - c := by
  induction c with
  | zero =>
      rw [Nat.add_zero, nat_sub_zero_clean]
  | succ c ih =>
      rw [Nat.add_succ]
      change a - Nat.succ (b + c) = a - b - Nat.succ c
      rw [Nat.sub_succ]
      rw [ih]
      rfl

private theorem factorialCount_succ (k : Nat) :
    bwordLength (natFactorialFn (natToUnary (Nat.succ k))) =
      bwordLength (natFactorialFn (natToUnary k)) * Nat.succ k := by
  have kUnary : UnaryHistory (natToUnary k) := natToUnary_unary k
  have step := natFactorialFn_succ (n := natToUnary k) kUnary
  have lengthStep := NatMul_bwordLength step
  change bwordLength (natFactorialFn (natToUnary (Nat.succ k))) =
    bwordLength (BHist.e1 (natToUnary k)) *
      bwordLength (natFactorialFn (natToUnary k)) at lengthStep
  rw [NatUp_unary_standard_bridge.right.left (natToUnary k) kUnary] at lengthStep
  rw [natToUnary_length] at lengthStep
  exact lengthStep.trans (Nat.mul_comm (Nat.succ k)
    (bwordLength (natFactorialFn (natToUnary k))))

theorem natFactorialCount_succ (k : Nat) :
    natFactorialCount (Nat.succ k) =
      natFactorialCount k * Nat.succ k := by
  exact factorialCount_succ k

private theorem natDescAux_succ_left_succ_right (n k : Nat) :
    natDescAux (Nat.succ n) (Nat.succ k) =
      natDescAux n k * (Nat.succ n) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      unfold natDescAux
      rw [Nat.succ_sub_succ_eq_sub]
      rw [ih]
      calc
        (natDescAux n k * Nat.succ n) * (n - k) =
            natDescAux n k * (Nat.succ n * (n - k)) :=
          nat_mul_assoc_clean (natDescAux n k) (Nat.succ n) (n - k)
        _ = natDescAux n k * ((n - k) * Nat.succ n) :=
          congrArg (fun t => natDescAux n k * t) (Nat.mul_comm (Nat.succ n) (n - k))
        _ = (natDescAux n k * (n - k)) * Nat.succ n :=
          (nat_mul_assoc_clean (natDescAux n k) (n - k) (Nat.succ n)).symm

private theorem nat_mul_right_add_factor (a b c : Nat) :
    a * c + b * c = (a + b) * c := by
  exact (nat_add_mul_clean a b c).symm

private theorem natDescAux_zero_tail_after_zero {n k : Nat} :
    natDescAux n k = 0 -> natDescAux n (Nat.succ k) = 0 := by
  intro zeroAtK
  change natDescAux n k * (n - k) = 0
  rw [zeroAtK, Nat.zero_mul]

private theorem natDescAux_zero_above (n extra : Nat) :
    natDescAux n (Nat.succ (n + extra)) = 0 := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      change natDescAux n n * (n - n) = 0
      rw [Nat.sub_self, Nat.mul_zero]
  | succ extra ih =>
      rw [Nat.add_succ]
      exact natDescAux_zero_tail_after_zero ih

private theorem natDescAux_zero_above_succ (n extra : Nat) :
    natDescAux n (Nat.succ n + extra) = 0 := by
  rw [Nat.succ_add]
  exact natDescAux_zero_above n extra

private theorem nat_self_add_tail (k extra : Nat) :
    k + extra - k = extra := by
  induction k with
  | zero =>
      rw [Nat.zero_add]
      exact nat_sub_zero_clean extra
  | succ k ih =>
      rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem nat_succ_split (k extra : Nat) :
    Nat.succ k + (k + extra - k) = Nat.succ (k + extra) := by
  rw [nat_self_add_tail]
  rw [Nat.succ_add]

private theorem natDescAux_zero_of_lt {n k : Nat} :
    n < k -> natDescAux n k = 0 := by
  intro hlt
  have hle : Nat.succ n ≤ k := Nat.succ_le_iff.mpr hlt
  cases Nat.le.dest hle with
  | intro extra eqk =>
      subst k
      exact natDescAux_zero_above_succ n extra

private theorem natDescAux_linear_factor_shift (n k : Nat) :
    natDescAux n k * Nat.succ k + natDescAux n k * (n - k) =
      natDescAux n k * Nat.succ n := by
  rw [(Nat.mul_add (natDescAux n k) (Nat.succ k) (n - k)).symm]
  by_cases hle : k ≤ n
  · cases Nat.le.dest hle with
    | intro extra eqn =>
        subst n
        exact congrArg (fun t => natDescAux (k + extra) k * t)
          (nat_succ_split k extra)
  · have hlt : n < k := Nat.lt_of_not_ge hle
    have zeroAtK : natDescAux n k = 0 := natDescAux_zero_of_lt hlt
    rw [zeroAtK, Nat.zero_mul, Nat.zero_mul]

private theorem natChooseCount_mul_factorial_eq_desc_aux :
    ∀ n k : Nat,
      natChooseCount n k * natFactorialCount k = natDescAux n k
  | 0, 0 => by
      rfl
  | 0, Nat.succ k => by
      unfold natChooseCount natChooseFn natFactorialCount
      rw [natToUnary_length, natToUnary_length]
      change 0 * bwordLength (natFactorialFn (natToUnary (Nat.succ k))) =
        natDescAux 0 (Nat.succ k)
      rw [Nat.zero_mul, natDescAux_zero_left]
  | Nat.succ n, 0 => by
      unfold natFactorialCount
      rw [natChooseCount_zero_right]
      rfl
  | Nat.succ n, Nat.succ k => by
      have leftIH :
          natChooseCount n k * natFactorialCount k = natDescAux n k :=
        natChooseCount_mul_factorial_eq_desc_aux n k
      have rightIH :
          natChooseCount n (Nat.succ k) * natFactorialCount (Nat.succ k) =
            natDescAux n (Nat.succ k) :=
        natChooseCount_mul_factorial_eq_desc_aux n (Nat.succ k)
      rw [natChooseCount_pascal, natFactorialCount_succ]
      calc
        (natChooseCount n k + natChooseCount n (Nat.succ k)) *
            (natFactorialCount k * Nat.succ k) =
            natChooseCount n k * (natFactorialCount k * Nat.succ k) +
              natChooseCount n (Nat.succ k) *
                (natFactorialCount k * Nat.succ k) :=
          nat_add_mul_clean (natChooseCount n k) (natChooseCount n (Nat.succ k))
            (natFactorialCount k * Nat.succ k)
        _ = (natChooseCount n k * natFactorialCount k) * Nat.succ k +
              natChooseCount n (Nat.succ k) *
                (natFactorialCount k * Nat.succ k) :=
          congrArg
            (fun t =>
              t + natChooseCount n (Nat.succ k) *
                (natFactorialCount k * Nat.succ k))
            (nat_mul_assoc_clean (natChooseCount n k)
              (natFactorialCount k) (Nat.succ k)).symm
        _ = (natChooseCount n k * natFactorialCount k) * Nat.succ k +
              natChooseCount n (Nat.succ k) *
                (natFactorialCount (Nat.succ k)) := by
          rw [natFactorialCount_succ]
        _ = natDescAux n k * Nat.succ k +
              natDescAux n (Nat.succ k) := by
          rw [leftIH, rightIH]
        _ = natDescAux n k * Nat.succ k +
              natDescAux n k * (n - k) := by
          rfl
        _ = (natDescAux n k * Nat.succ n) := by
          change natDescAux n k * Nat.succ k +
              natDescAux n k * (n - k) =
            natDescAux n k * Nat.succ n
          exact natDescAux_linear_factor_shift n k
        _ = natDescAux (Nat.succ n) (Nat.succ k) :=
          (natDescAux_succ_left_succ_right n k).symm

theorem natChooseCount_mul_factorial_eq_desc (n k : Nat) :
    natChooseCount n k * natFactorialCount k = natDescPochhammerCount n k :=
  natChooseCount_mul_factorial_eq_desc_aux n k

private theorem natDescAux_add_split (n m k : Nat) :
    natDescAux n m * natDescAux (n - m) k = natDescAux n (m + k) := by
  induction k with
  | zero =>
      rw [Nat.add_zero]
      change natDescAux n m * 1 = natDescAux n m
      exact Nat.mul_one _
  | succ k ih =>
      rw [Nat.add_succ]
      change natDescAux n m *
          (natDescAux (n - m) k * (n - m - k)) =
        natDescAux n (m + k) * (n - (m + k))
      calc
        natDescAux n m * (natDescAux (n - m) k * (n - m - k)) =
            (natDescAux n m * natDescAux (n - m) k) * (n - m - k) :=
          (nat_mul_assoc_clean (natDescAux n m)
            (natDescAux (n - m) k) (n - m - k)).symm
        _ = natDescAux n (m + k) * (n - m - k) :=
          congrArg (fun t => t * (n - m - k)) ih
        _ = natDescAux n (m + k) * (n - (m + k)) :=
          congrArg (fun t => natDescAux n (m + k) * t)
            (nat_sub_add_eq_clean n m k).symm

theorem natChooseFn_zero_right_hsame (n : Nat) :
    hsame (natChooseFn (natToUnary n) BHist.Empty) NatOne := by
  have chooseUnary :
      UnaryHistory (natChooseFn (natToUnary n) BHist.Empty) :=
    natChooseFn_unary_result
  apply (NatUp_unary_standard_bridge.right.right.right.left
    chooseUnary (unary_e1_closed unary_empty)).mpr
  unfold natChooseFn
  rw [natToUnary_length]
  cases n <;> rfl

theorem natChooseFn_mul_factorial_zero_hsame_desc (n : Nat) :
    hsame
      (natMulFn
        (natChooseFn (natToUnary n) BHist.Empty)
        (natFactorialFn BHist.Empty))
      (natDescPochhammerFn (natToUnary n) BHist.Empty) := by
  have chooseUnary :
      UnaryHistory (natChooseFn (natToUnary n) BHist.Empty) :=
    natChooseFn_unary_result
  change hsame
    (natMulFn (natChooseFn (natToUnary n) BHist.Empty) NatOne)
    NatOne
  exact hsame_trans
    (NatMul_unit_right_hsame
      (natMulFn_rel chooseUnary (unary_e1_closed unary_empty)))
    (natChooseFn_zero_right_hsame n)

theorem natChooseFn_mul_factorial_hsame_desc (n k : Nat) :
    hsame
      (natMulFn
        (natChooseFn (natToUnary n) (natToUnary k))
        (natFactorialFn (natToUnary k)))
      (natDescPochhammerFn (natToUnary n) (natToUnary k)) := by
  have chooseUnary :
      UnaryHistory (natChooseFn (natToUnary n) (natToUnary k)) :=
    natChooseFn_unary_result
  have factorialUnary :
      UnaryHistory (natFactorialFn (natToUnary k)) :=
    natFactorialFn_unary (natToUnary_unary k)
  have productUnary :
      UnaryHistory
        (natMulFn
          (natChooseFn (natToUnary n) (natToUnary k))
          (natFactorialFn (natToUnary k))) :=
    natMulFn_unary chooseUnary factorialUnary
  have descUnary :
      UnaryHistory (natDescPochhammerFn (natToUnary n) (natToUnary k)) :=
    natDescPochhammerFn_unary _ _
  apply (NatUp_unary_standard_bridge.right.right.right.left productUnary descUnary).mpr
  rw [natMulFn_bwordLength chooseUnary factorialUnary]
  unfold natDescPochhammerFn
  repeat rw [natToUnary_length]
  change natChooseCount n k * natFactorialCount k = natDescPochhammerCount n k
  exact natChooseCount_mul_factorial_eq_desc n k

theorem natDescPochhammerFn_add_split_hsame (n m k : Nat) :
    hsame
      (natDescPochhammerFn (natToUnary n) (natToUnary (m + k)))
      (natMulFn
        (natDescPochhammerFn (natToUnary n) (natToUnary m))
        (natDescPochhammerFn (natToUnary (n - m)) (natToUnary k))) := by
  have leftUnary :
      UnaryHistory (natDescPochhammerFn (natToUnary n) (natToUnary (m + k))) :=
    natDescPochhammerFn_unary _ _
  have rightLeftUnary :
      UnaryHistory (natDescPochhammerFn (natToUnary n) (natToUnary m)) :=
    natDescPochhammerFn_unary _ _
  have rightRightUnary :
      UnaryHistory (natDescPochhammerFn (natToUnary (n - m)) (natToUnary k)) :=
    natDescPochhammerFn_unary _ _
  have rightUnary :
      UnaryHistory
        (natMulFn
          (natDescPochhammerFn (natToUnary n) (natToUnary m))
          (natDescPochhammerFn (natToUnary (n - m)) (natToUnary k))) :=
    natMulFn_unary rightLeftUnary rightRightUnary
  apply hsame_symm
  apply (NatUp_unary_standard_bridge.right.right.right.left rightUnary leftUnary).mpr
  rw [natMulFn_bwordLength rightLeftUnary rightRightUnary]
  unfold natDescPochhammerFn
  repeat rw [natToUnary_length]
  unfold natDescPochhammerCount
  exact natDescAux_add_split n m k

theorem PochhammerUp_constructive_export :
    (∀ x : Z, Zeq (descPochhammerInt x 0) integerRing.one) ∧
      (∀ x : Z, Zeq (ascPochhammerInt x 0) integerRing.one) ∧
      (∀ x : Z, Zeq (descPochhammerInt x 1) x) ∧
      (∀ x : Z, Zeq (ascPochhammerInt x 1) x) ∧
      (∀ n : Nat,
        hsame
          (natMulFn
            (natChooseFn (natToUnary n) BHist.Empty)
            (natFactorialFn BHist.Empty))
          (natDescPochhammerFn (natToUnary n) BHist.Empty)) ∧
      (∀ n k : Nat,
        hsame
          (natMulFn
            (natChooseFn (natToUnary n) (natToUnary k))
            (natFactorialFn (natToUnary k)))
          (natDescPochhammerFn (natToUnary n) (natToUnary k))) ∧
      (∀ n m k : Nat,
        hsame
          (natDescPochhammerFn (natToUnary n) (natToUnary (m + k)))
          (natMulFn
            (natDescPochhammerFn (natToUnary n) (natToUnary m))
            (natDescPochhammerFn (natToUnary (n - m)) (natToUnary k)))) := by
  constructor
  · intro x
    exact descPochhammerInt_zero x
  · constructor
    · intro x
      exact ascPochhammerInt_zero x
    · constructor
      · intro x
        exact descPochhammerInt_one x
      · constructor
        · intro x
          exact ascPochhammerInt_one x
        · constructor
          · intro n
            exact natChooseFn_mul_factorial_zero_hsame_desc n
          · constructor
            · intro n k
              exact natChooseFn_mul_factorial_hsame_desc n k
            · intro n m k
              exact natDescPochhammerFn_add_split_hsame n m k

end BEDC.Derived.PochhammerUp
