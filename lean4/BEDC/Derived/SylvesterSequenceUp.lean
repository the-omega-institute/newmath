import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.GcdUp

namespace BEDC.Derived.SylvesterSequenceUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

/- Sylvester 序列的核心导出保持在 Nat/List 层，只使用显式递归与构造性算术。 -/
def sylvester : Nat -> Nat
  | 0 => 2
  | n + 1 => sylvester n * sylvester n - sylvester n + 1

def prefixProduct : Nat -> Nat
  | 0 => 1
  | n + 1 => prefixProduct n * sylvester n

private theorem nat_add_zero_right : forall a : Nat, a + 0 = a
  | 0 => by
      rfl
  | a + 1 => by
      change (a + 0).succ = a.succ
      rw [nat_add_zero_right a]

private theorem nat_add_sub_cancel_right : forall a b : Nat, (a + b) - b = a
  | a, 0 => by
      exact nat_add_zero_right a
  | a, b + 1 => by
      rw [Nat.add_succ]
      rw [Nat.succ_sub_succ_eq_sub]
      exact nat_add_sub_cancel_right a b

private theorem nat_mul_assoc_right : forall a b c : Nat, (a * b) * c = a * (b * c)
  | a, b, 0 => by
      rw [Nat.mul_zero]
      rw [Nat.mul_zero]
      rw [Nat.mul_zero]
  | a, b, c + 1 => by
      rw [Nat.mul_succ]
      rw [Nat.mul_succ]
      rw [Nat.mul_add]
      rw [nat_mul_assoc_right a b c]

private theorem nat_dvd_mul_right_of_dvd {a b : Nat} (c : Nat) :
    a ∣ b -> a ∣ b * c := by
  intro h
  cases h with
  | intro q hb =>
      exists q * c
      rw [hb]
      exact nat_mul_assoc_right a q c

private theorem nat_dvd_trans {a b c : Nat} :
    a ∣ b -> b ∣ c -> a ∣ c := by
  intro hab hbc
  cases hab with
  | intro q hb =>
      cases hbc with
      | intro r hc =>
          exists q * r
          rw [hc, hb]
          exact nat_mul_assoc_right a q r

private theorem nat_add_right_cancel : forall a b c : Nat, a + c = b + c -> a = b
  | a, b, 0 => by
      rw [nat_add_zero_right a]
      rw [nat_add_zero_right b]
      intro h
      exact h
  | a, b, c + 1 => by
      rw [Nat.add_succ]
      rw [Nat.add_succ]
      intro h
      exact nat_add_right_cancel a b c (Nat.succ.inj h)

private theorem nat_add_succ_shift : forall a c : Nat, (a + c) + 1 = (a + 1) + c
  | a, 0 => by
      rw [nat_add_zero_right]
  | a, c + 1 => by
      rw [Nat.add_succ]
      rw [Nat.add_succ]
      exact congrArg Nat.succ (nat_add_succ_shift a c)

private theorem nat_one_ne_add_two_tail (x d : Nat) :
    1 = x + (d + 2) -> False := by
  intro h
  change 1 = Nat.succ (Nat.succ (x + d)) at h
  have h0 : 0 = Nat.succ (x + d) := Nat.succ.inj h
  exact Nat.noConfusion h0

private theorem nat_no_between_multiples :
    forall d q r : Nat, (d + 2) * q + 1 = (d + 2) * r -> False
  | d, 0, r => by
      intro h
      cases r with
      | zero =>
          change 1 = 0 at h
          cases h
      | succ r =>
          change 1 = (d + 2) * r + (d + 2) at h
          exact nat_one_ne_add_two_tail ((d + 2) * r) d h
  | d, q + 1, r => by
      intro h
      cases r with
      | zero =>
          change ((d + 2) * q + (d + 2)) + 1 = 0 at h
          exact Nat.noConfusion h
      | succ r =>
          change ((d + 2) * q + (d + 2)) + 1 = (d + 2) * r + (d + 2) at h
          have shifted :
              ((d + 2) * q + 1) + (d + 2) = (d + 2) * r + (d + 2) :=
            Eq.trans (nat_add_succ_shift ((d + 2) * q) (d + 2)).symm h
          have hrec : (d + 2) * q + 1 = (d + 2) * r :=
            nat_add_right_cancel ((d + 2) * q + 1) ((d + 2) * r) (d + 2) shifted
          exact nat_no_between_multiples d q r hrec

private theorem nat_common_divisor_consecutive_one {d p : Nat} :
    d ∣ p -> d ∣ p + 1 -> d = 1 := by
  intro hdp hdps
  cases hdp with
  | intro q hp =>
      cases hdps with
      | intro r hps =>
          cases d with
          | zero =>
              rw [Nat.zero_mul] at hp
              rw [hp] at hps
              rw [Nat.zero_mul] at hps
              cases hps
          | succ d =>
              cases d with
              | zero =>
                  rfl
              | succ d =>
                  have impossible : False := by
                    apply nat_no_between_multiples d q r
                    rw [← hp]
                    exact hps
                  exact False.elim impossible

theorem sylvester_zero :
    sylvester 0 = 2 := by
  rfl

theorem sylvester_succ_recurrence (n : Nat) :
    sylvester (n + 1) = sylvester n * sylvester n - sylvester n + 1 := by
  rfl

theorem prefixProduct_zero :
    prefixProduct 0 = 1 := by
  rfl

theorem prefixProduct_succ (n : Nat) :
    prefixProduct (n + 1) = prefixProduct n * sylvester n := by
  rfl

theorem sylvester_eq_prefixProduct_succ :
    forall n : Nat, sylvester n = prefixProduct n + 1
  | 0 => by
      rfl
  | n + 1 => by
      unfold sylvester prefixProduct
      have ih : sylvester n = prefixProduct n + 1 :=
        sylvester_eq_prefixProduct_succ n
      rw [ih]
      rw [Nat.mul_succ]
      rw [nat_add_sub_cancel_right]
      rw [Nat.succ_mul]
      rw [Nat.mul_succ]

theorem sylvester_succ_eq_product_le_plus_one (n : Nat) :
    sylvester (n + 1) = prefixProduct (n + 1) + 1 :=
  sylvester_eq_prefixProduct_succ (n + 1)

theorem sylvester_succ_eq_previous_product_mul_plus_one (n : Nat) :
    sylvester (n + 1) = prefixProduct n * sylvester n + 1 := by
  exact sylvester_eq_prefixProduct_succ (n + 1)

theorem sylvester_pos (n : Nat) :
    0 < sylvester n := by
  rw [sylvester_eq_prefixProduct_succ n]
  exact Nat.succ_pos _

theorem sylvester_ne_zero (n : Nat) :
    sylvester n ≠ 0 :=
  Nat.ne_of_gt (sylvester_pos n)

theorem prefixProduct_pos :
    forall n : Nat, 0 < prefixProduct n
  | 0 => by
      exact Nat.succ_pos 0
  | n + 1 => by
      rw [prefixProduct_succ]
      exact Nat.mul_pos (prefixProduct_pos n) (sylvester_pos n)

theorem prefixProduct_ne_zero (n : Nat) :
    prefixProduct n ≠ 0 :=
  Nat.ne_of_gt (prefixProduct_pos n)

theorem sylvester_dvd_prefixProduct_of_lt {m n : Nat} :
    m < n -> sylvester m ∣ prefixProduct n := by
  intro h
  induction n with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ h)
  | succ n ih =>
      rw [prefixProduct_succ]
      have hm : m < n ∨ m = n :=
        Nat.lt_succ_iff_lt_or_eq.mp h
      cases hm with
      | inl hlt =>
          exact nat_dvd_mul_right_of_dvd (sylvester n) (ih hlt)
      | inr heq =>
          rw [heq]
          exact Nat.dvd_mul_left (sylvester n) (prefixProduct n)

def NatCommonDivisorOne (a b : Nat) : Prop :=
  forall d : Nat, d ∣ a -> d ∣ b -> d = 1

theorem sylvester_common_divisor_one_of_lt {m n : Nat} :
    m < n -> NatCommonDivisorOne (sylvester m) (sylvester n) := by
  intro h d dDividesLeft dDividesRight
  have dDividesProduct : d ∣ prefixProduct n :=
    nat_dvd_trans dDividesLeft (sylvester_dvd_prefixProduct_of_lt h)
  rw [sylvester_eq_prefixProduct_succ n] at dDividesRight
  exact nat_common_divisor_consecutive_one dDividesProduct dDividesRight

theorem sylvester_pairwise_coprime_ordered :
    forall {m n : Nat}, m < n -> NatCommonDivisorOne (sylvester m) (sylvester n) := by
  intro m n h
  exact sylvester_common_divisor_one_of_lt h

structure NatRat where
  num : Nat
  den : Nat

def NatRatEq (x y : NatRat) : Prop :=
  x.num * y.den = y.num * x.den

def natRatOne : NatRat :=
  { num := 1, den := 1 }

def sylvesterPartialSumClosed (n : Nat) : NatRat :=
  { num := prefixProduct (n + 1) - 1, den := prefixProduct (n + 1) }

def sylvesterPartialComplement (n : Nat) : NatRat :=
  { num := 1, den := prefixProduct (n + 1) }

def natRatAdd (x y : NatRat) : NatRat :=
  { num := x.num * y.den + y.num * x.den, den := x.den * y.den }

theorem sylvesterPartialSumClosed_den_pos (n : Nat) :
    0 < (sylvesterPartialSumClosed n).den :=
  prefixProduct_pos (n + 1)

theorem sylvesterPartialComplement_den_pos (n : Nat) :
    0 < (sylvesterPartialComplement n).den :=
  prefixProduct_pos (n + 1)

private theorem pred_mul_add_self_eq_square {p : Nat} :
    0 < p -> (p - 1) * p + p = p * p := by
  cases p with
  | zero =>
      intro hp
      exact False.elim (Nat.not_lt_zero _ hp)
  | succ p =>
      intro _hp
      change p * (p + 1) + (p + 1) = (p + 1) * (p + 1)
      rw [Nat.succ_mul]

theorem sylvesterPartialSumClosed_add_complement_eq_one (n : Nat) :
    NatRatEq
      (natRatAdd (sylvesterPartialSumClosed n) (sylvesterPartialComplement n))
      natRatOne := by
  unfold NatRatEq natRatAdd sylvesterPartialSumClosed sylvesterPartialComplement natRatOne
  change
    (((prefixProduct (n + 1) - 1) * prefixProduct (n + 1) +
          1 * prefixProduct (n + 1)) *
        1 =
      1 * (prefixProduct (n + 1) * prefixProduct (n + 1)))
  rw [Nat.mul_one, Nat.one_mul (prefixProduct (n + 1))]
  exact (pred_mul_add_self_eq_square (prefixProduct_pos (n + 1))).trans
    (Nat.one_mul (prefixProduct (n + 1) * prefixProduct (n + 1))).symm

def natToIntegerUp (n : Nat) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat
    (BEDC.Derived.IntUp.natToUnary n)
    (BEDC.Derived.IntUp.natToUnary_unary n)

def sylvesterInteger (n : Nat) : IntegerUp :=
  natToIntegerUp (sylvester n)

def sylvesterIntegerPrefixList : Nat -> List IntegerUp
  | 0 => []
  | n + 1 => sylvesterInteger n :: sylvesterIntegerPrefixList n

def sylvesterIntegerFoldProduct (n : Nat) : IntegerUp :=
  listProd IntegerUp_RelCommRing (sylvesterIntegerPrefixList n)

theorem sylvesterIntegerFoldProduct_zero :
    IntEq (sylvesterIntegerFoldProduct 0) intOne := by
  exact prod_nil IntegerUp_RelCommRing

theorem sylvesterIntegerFoldProduct_succ (n : Nat) :
    IntEq (sylvesterIntegerFoldProduct (n + 1))
      (IntMul (sylvesterInteger n) (sylvesterIntegerFoldProduct n)) := by
  exact prod_cons IntegerUp_RelCommRing
    (sylvesterInteger n) (sylvesterIntegerPrefixList n)

/- GcdUp 的 BHist 层目前没有从 Nat 除法证明直接搬运互素的公开桥；这里保持缺席。 -/
def sylvesterUnary (n : Nat) : BHist :=
  BEDC.Derived.IntUp.natToUnary (sylvester n)

theorem sylvesterUnary_unary (n : Nat) :
    UnaryHistory (sylvesterUnary n) :=
  BEDC.Derived.IntUp.natToUnary_unary (sylvester n)

end BEDC.Derived.SylvesterSequenceUp
