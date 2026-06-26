import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.FactorialUp
import BEDC.Derived.IntUp.CommRing
import BEDC.Derived.PochhammerUp

namespace BEDC.Derived.MultinomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.FactorialUp
open BEDC.Derived.IntUp

abbrev Z : Type := BEDC.Algebra.Rel.IntegerUp
abbrev Zeq : Z -> Z -> Prop := BEDC.Algebra.Rel.IntEq

def integerRing : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def multinomialWeight : List Nat -> Nat
  | [] => 0
  | k :: ks => k + multinomialWeight ks

def multinomialCount : List Nat -> Nat
  | [] => 1
  | k :: ks =>
      BEDC.Derived.PochhammerUp.natChooseCount (k + multinomialWeight ks) k *
        multinomialCount ks

def multinomialFactorialNumerator (ks : List Nat) : Nat :=
  BEDC.Derived.PochhammerUp.natFactorialCount (multinomialWeight ks)

def multinomialFactorialDenominator : List Nat -> Nat
  | [] => 1
  | k :: ks =>
      BEDC.Derived.PochhammerUp.natFactorialCount k *
        multinomialFactorialDenominator ks

def multinomialIndexTotal (n : Nat) (ks : List Nat) : Prop :=
  multinomialWeight ks = n

def multinomialFn (ks : List BHist) : BHist :=
  natToUnary (multinomialCount (ks.map bwordLength))

def multinomialInt (ks : List Nat) : Z :=
  BEDC.Derived.RationalUp.intOfNat
    (natToUnary (multinomialCount ks))
    (natToUnary_unary (multinomialCount ks))

def multinomialIntUp (ks : List BHist) : Z :=
  BEDC.Derived.RationalUp.intOfNat
    (multinomialFn ks)
    (natToUnary_unary (multinomialCount (ks.map bwordLength)))

theorem multinomialWeight_nil :
    multinomialWeight [] = 0 := by
  rfl

theorem multinomialWeight_cons (k : Nat) (ks : List Nat) :
    multinomialWeight (k :: ks) = k + multinomialWeight ks := by
  rfl

theorem multinomialCount_nil :
    multinomialCount [] = 1 := by
  rfl

theorem multinomialCount_cons (k : Nat) (ks : List Nat) :
    multinomialCount (k :: ks) =
      BEDC.Derived.PochhammerUp.natChooseCount (k + multinomialWeight ks) k *
        multinomialCount ks := by
  rfl

theorem multinomialFactorialDenominator_nil :
    multinomialFactorialDenominator [] = 1 := by
  rfl

theorem multinomialFactorialDenominator_cons (k : Nat) (ks : List Nat) :
    multinomialFactorialDenominator (k :: ks) =
      BEDC.Derived.PochhammerUp.natFactorialCount k *
        multinomialFactorialDenominator ks := by
  rfl

theorem multinomialFn_unary_result (ks : List BHist) :
    UnaryHistory (multinomialFn ks) := by
  unfold multinomialFn
  exact natToUnary_unary _

theorem multinomialFn_length (ks : List BHist) :
    bwordLength (multinomialFn ks) =
      multinomialCount (ks.map bwordLength) := by
  unfold multinomialFn
  exact natToUnary_length _

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

private theorem nat_mul_four_reorder (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  calc
    (a * b) * (c * d) = a * (b * (c * d)) :=
      nat_mul_assoc_clean a b (c * d)
    _ = a * ((b * c) * d) :=
      congrArg (fun x => a * x) (nat_mul_assoc_clean b c d).symm
    _ = a * ((c * b) * d) :=
      congrArg (fun x => a * (x * d)) (Nat.mul_comm b c)
    _ = a * (c * (b * d)) :=
      congrArg (fun x => a * x) (nat_mul_assoc_clean c b d)
    _ = (a * c) * (b * d) :=
      (nat_mul_assoc_clean a c (b * d)).symm

private theorem nat_sub_zero_clean (n : Nat) : n - 0 = n := by
  induction n with
  | zero =>
      rfl
  | succ _ih =>
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

private theorem nat_self_add_tail (k extra : Nat) :
    k + extra - k = extra := by
  induction k with
  | zero =>
      rw [Nat.zero_add]
      exact nat_sub_zero_clean extra
  | succ k ih =>
      rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem natDescPochhammerCount_succ_left_succ_right (n k : Nat) :
    BEDC.Derived.PochhammerUp.natDescPochhammerCount (Nat.succ n) (Nat.succ k) =
      BEDC.Derived.PochhammerUp.natDescPochhammerCount n k * Nat.succ n := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [BEDC.Derived.PochhammerUp.natDescPochhammerCount_succ
        (Nat.succ n) (Nat.succ k)]
      rw [Nat.succ_sub_succ_eq_sub]
      rw [ih]
      rw [BEDC.Derived.PochhammerUp.natDescPochhammerCount_succ n k]
      calc
        (BEDC.Derived.PochhammerUp.natDescPochhammerCount n k * Nat.succ n) *
            (n - k) =
            BEDC.Derived.PochhammerUp.natDescPochhammerCount n k *
              (Nat.succ n * (n - k)) :=
          nat_mul_assoc_clean
            (BEDC.Derived.PochhammerUp.natDescPochhammerCount n k)
            (Nat.succ n) (n - k)
        _ = BEDC.Derived.PochhammerUp.natDescPochhammerCount n k *
              ((n - k) * Nat.succ n) :=
          congrArg
            (fun x => BEDC.Derived.PochhammerUp.natDescPochhammerCount n k * x)
            (Nat.mul_comm (Nat.succ n) (n - k))
        _ = (BEDC.Derived.PochhammerUp.natDescPochhammerCount n k * (n - k)) *
              Nat.succ n :=
          (nat_mul_assoc_clean
            (BEDC.Derived.PochhammerUp.natDescPochhammerCount n k)
            (n - k) (Nat.succ n)).symm

private theorem natDescPochhammerCount_self_factorial :
    ∀ n : Nat,
      BEDC.Derived.PochhammerUp.natDescPochhammerCount n n =
        BEDC.Derived.PochhammerUp.natFactorialCount n
  | 0 => by
      rfl
  | Nat.succ n => by
      rw [natDescPochhammerCount_succ_left_succ_right]
      rw [natDescPochhammerCount_self_factorial n]
      rw [BEDC.Derived.PochhammerUp.natFactorialCount_succ]

private theorem natDescPochhammerCount_add_split (n m k : Nat) :
    BEDC.Derived.PochhammerUp.natDescPochhammerCount n m *
        BEDC.Derived.PochhammerUp.natDescPochhammerCount (n - m) k =
      BEDC.Derived.PochhammerUp.natDescPochhammerCount n (m + k) := by
  induction k with
  | zero =>
      rw [Nat.add_zero]
      change BEDC.Derived.PochhammerUp.natDescPochhammerCount n m * 1 =
        BEDC.Derived.PochhammerUp.natDescPochhammerCount n m
      exact Nat.mul_one _
  | succ k ih =>
      change BEDC.Derived.PochhammerUp.natDescPochhammerCount n m *
          BEDC.Derived.PochhammerUp.natDescPochhammerCount (n - m) (Nat.succ k) =
        BEDC.Derived.PochhammerUp.natDescPochhammerCount n (Nat.succ (m + k))
      rw [BEDC.Derived.PochhammerUp.natDescPochhammerCount_succ (n - m) k]
      rw [BEDC.Derived.PochhammerUp.natDescPochhammerCount_succ n (m + k)]
      calc
        BEDC.Derived.PochhammerUp.natDescPochhammerCount n m *
            (BEDC.Derived.PochhammerUp.natDescPochhammerCount (n - m) k *
              (n - m - k)) =
            (BEDC.Derived.PochhammerUp.natDescPochhammerCount n m *
              BEDC.Derived.PochhammerUp.natDescPochhammerCount (n - m) k) *
              (n - m - k) :=
          (nat_mul_assoc_clean
            (BEDC.Derived.PochhammerUp.natDescPochhammerCount n m)
            (BEDC.Derived.PochhammerUp.natDescPochhammerCount (n - m) k)
            (n - m - k)).symm
        _ = BEDC.Derived.PochhammerUp.natDescPochhammerCount n (m + k) *
              (n - m - k) :=
          congrArg (fun x => x * (n - m - k)) ih
        _ = BEDC.Derived.PochhammerUp.natDescPochhammerCount n (m + k) *
              (n - (m + k)) :=
          congrArg
            (fun x => BEDC.Derived.PochhammerUp.natDescPochhammerCount n (m + k) * x)
            (nat_sub_add_eq_clean n m k).symm

theorem multinomialCount_singleton (k : Nat) :
    multinomialCount [k] = 1 := by
  change BEDC.Derived.PochhammerUp.natChooseCount (k + 0) k * 1 = 1
  rw [Nat.add_zero]
  unfold BEDC.Derived.PochhammerUp.natChooseCount natChooseFn
  repeat rw [natToUnary_length]
  rw [chooseCount_self]

theorem multinomialFn_singleton_hsame (k : BHist) :
    hsame (multinomialFn [k]) NatOne := by
  have leftUnary : UnaryHistory (multinomialFn [k]) :=
    multinomialFn_unary_result [k]
  have rightUnary : UnaryHistory NatOne :=
    unary_e1_closed unary_empty
  apply (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
    leftUnary rightUnary).mpr
  rw [multinomialFn_length]
  change multinomialCount [bwordLength k] = bwordLength NatOne
  rw [multinomialCount_singleton]
  rfl

theorem multinomialCount_pair (k l : Nat) :
    multinomialCount [k, l] =
      BEDC.Derived.PochhammerUp.natChooseCount (k + l) k := by
  change BEDC.Derived.PochhammerUp.natChooseCount (k + (l + 0)) k *
      (BEDC.Derived.PochhammerUp.natChooseCount (l + 0) l * 1) =
    BEDC.Derived.PochhammerUp.natChooseCount (k + l) k
  rw [Nat.add_zero]
  unfold BEDC.Derived.PochhammerUp.natChooseCount natChooseFn
  repeat rw [natToUnary_length]
  rw [chooseCount_self]
  rw [Nat.mul_one]

theorem multinomialFn_pair_length (k l : BHist) :
    bwordLength (multinomialFn [k, l]) =
      bwordLength (natChooseFn
        (natToUnary (bwordLength k + bwordLength l))
        (natToUnary (bwordLength k))) := by
  rw [multinomialFn_length]
  change multinomialCount [bwordLength k, bwordLength l] =
    bwordLength
      (natChooseFn
        (natToUnary (bwordLength k + bwordLength l))
        (natToUnary (bwordLength k)))
  rw [multinomialCount_pair]
  unfold BEDC.Derived.PochhammerUp.natChooseCount
  rfl

theorem multinomialFn_pair_binomial_hsame (k l : BHist) :
    hsame (multinomialFn [k, l])
      (natChooseFn
        (natToUnary (bwordLength k + bwordLength l))
        (natToUnary (bwordLength k))) := by
  have leftUnary : UnaryHistory (multinomialFn [k, l]) :=
    multinomialFn_unary_result [k, l]
  have rightUnary :
      UnaryHistory
        (natChooseFn
          (natToUnary (bwordLength k + bwordLength l))
          (natToUnary (bwordLength k))) :=
    natChooseFn_unary_result
  apply (BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.right.right.left
    leftUnary rightUnary).mpr
  exact multinomialFn_pair_length k l

theorem multinomialCount_pascal (k : Nat) (ks : List Nat) :
    multinomialCount (Nat.succ k :: ks) =
      BEDC.Derived.PochhammerUp.natChooseCount
          (Nat.succ k + multinomialWeight ks) (Nat.succ k) *
        multinomialCount ks := by
  rfl

theorem multinomialCount_pascal_expanded (k : Nat) (ks : List Nat) :
    multinomialCount (Nat.succ k :: ks) =
      (BEDC.Derived.PochhammerUp.natChooseCount
          (k + multinomialWeight ks) k +
        BEDC.Derived.PochhammerUp.natChooseCount
          (k + multinomialWeight ks) (Nat.succ k)) *
        multinomialCount ks := by
  rw [multinomialCount_pascal]
  rw [Nat.succ_add]
  have pascal :=
    BEDC.Derived.PochhammerUp.natChooseCount_pascal
      (k + multinomialWeight ks) k
  change BEDC.Derived.PochhammerUp.natChooseCount
      (Nat.succ (k + multinomialWeight ks)) (Nat.succ k) *
        multinomialCount ks =
      (BEDC.Derived.PochhammerUp.natChooseCount
        (k + multinomialWeight ks) k +
      BEDC.Derived.PochhammerUp.natChooseCount
        (k + multinomialWeight ks) (Nat.succ k)) *
      multinomialCount ks
  rw [pascal]

theorem multinomialFactorialQuotient_identity :
    ∀ ks : List Nat,
      multinomialCount ks * multinomialFactorialDenominator ks =
        multinomialFactorialNumerator ks
  | [] => by
      rfl
  | k :: ks => by
      have ih :
          multinomialCount ks * multinomialFactorialDenominator ks =
            multinomialFactorialNumerator ks :=
        multinomialFactorialQuotient_identity ks
      unfold multinomialFactorialNumerator at ih
      rw [multinomialCount_cons]
      rw [multinomialFactorialDenominator_cons]
      unfold multinomialFactorialNumerator
      change
        (BEDC.Derived.PochhammerUp.natChooseCount
            (k + multinomialWeight ks) k *
          multinomialCount ks) *
            (BEDC.Derived.PochhammerUp.natFactorialCount k *
              multinomialFactorialDenominator ks) =
          BEDC.Derived.PochhammerUp.natFactorialCount
            (k + multinomialWeight ks)
      have split :=
        natDescPochhammerCount_add_split
          (k + multinomialWeight ks) k (multinomialWeight ks)
      rw [nat_self_add_tail] at split
      calc
        (BEDC.Derived.PochhammerUp.natChooseCount
            (k + multinomialWeight ks) k *
          multinomialCount ks) *
            (BEDC.Derived.PochhammerUp.natFactorialCount k *
              multinomialFactorialDenominator ks) =
            (BEDC.Derived.PochhammerUp.natChooseCount
              (k + multinomialWeight ks) k *
              BEDC.Derived.PochhammerUp.natFactorialCount k) *
              (multinomialCount ks * multinomialFactorialDenominator ks) :=
          nat_mul_four_reorder
            (BEDC.Derived.PochhammerUp.natChooseCount
              (k + multinomialWeight ks) k)
            (multinomialCount ks)
            (BEDC.Derived.PochhammerUp.natFactorialCount k)
            (multinomialFactorialDenominator ks)
        _ = BEDC.Derived.PochhammerUp.natDescPochhammerCount
              (k + multinomialWeight ks) k *
              BEDC.Derived.PochhammerUp.natFactorialCount
                (multinomialWeight ks) := by
          rw [BEDC.Derived.PochhammerUp.natChooseCount_mul_factorial_eq_desc]
          rw [ih]
        _ = BEDC.Derived.PochhammerUp.natDescPochhammerCount
              (k + multinomialWeight ks) k *
              BEDC.Derived.PochhammerUp.natDescPochhammerCount
                (multinomialWeight ks) (multinomialWeight ks) := by
          rw [natDescPochhammerCount_self_factorial]
        _ = BEDC.Derived.PochhammerUp.natDescPochhammerCount
              (k + multinomialWeight ks) (k + multinomialWeight ks) :=
          split
        _ = BEDC.Derived.PochhammerUp.natFactorialCount
              (k + multinomialWeight ks) :=
          natDescPochhammerCount_self_factorial (k + multinomialWeight ks)

theorem multinomialFactorialQuotient_total
    (n : Nat) (ks : List Nat) (h : multinomialIndexTotal n ks) :
    multinomialCount ks * multinomialFactorialDenominator ks =
      BEDC.Derived.PochhammerUp.natFactorialCount n := by
  unfold multinomialIndexTotal at h
  rw [multinomialFactorialQuotient_identity]
  unfold multinomialFactorialNumerator
  rw [h]

theorem multinomialFactorialDivisibility
    (n : Nat) (ks : List Nat) (h : multinomialIndexTotal n ks) :
    ∃ q : Nat,
      q * multinomialFactorialDenominator ks =
        BEDC.Derived.PochhammerUp.natFactorialCount n := by
  exact ⟨multinomialCount ks, multinomialFactorialQuotient_total n ks h⟩

theorem multinomialIntegral_witness (ks : List Nat) :
    ∃ z : Z, Zeq z (multinomialInt ks) := by
  exact ⟨multinomialInt ks, integerRing.refl (multinomialInt ks)⟩

theorem multinomialIntegral_up_witness (ks : List BHist) :
    ∃ z : Z, Zeq z (multinomialIntUp ks) := by
  exact ⟨multinomialIntUp ks, integerRing.refl (multinomialIntUp ks)⟩

theorem MultinomialUp_constructive_export :
    (∀ ks : List BHist, UnaryHistory (multinomialFn ks)) ∧
      (∀ k l : BHist,
        hsame (multinomialFn [k, l])
          (natChooseFn
            (natToUnary (bwordLength k + bwordLength l))
            (natToUnary (bwordLength k)))) ∧
      (∀ k : Nat, ∀ ks : List Nat,
        multinomialCount (Nat.succ k :: ks) =
          (BEDC.Derived.PochhammerUp.natChooseCount
              (k + multinomialWeight ks) k +
            BEDC.Derived.PochhammerUp.natChooseCount
              (k + multinomialWeight ks) (Nat.succ k)) *
            multinomialCount ks) ∧
      (∀ ks : List Nat,
        multinomialCount ks * multinomialFactorialDenominator ks =
          multinomialFactorialNumerator ks) ∧
      (∀ n : Nat, ∀ ks : List Nat, multinomialIndexTotal n ks ->
        ∃ q : Nat,
          q * multinomialFactorialDenominator ks =
            BEDC.Derived.PochhammerUp.natFactorialCount n) ∧
      (∀ ks : List Nat, ∃ z : Z, Zeq z (multinomialInt ks)) := by
  constructor
  · intro ks
    exact multinomialFn_unary_result ks
  · constructor
    · intro k l
      exact multinomialFn_pair_binomial_hsame k l
    · constructor
      · intro k ks
        exact multinomialCount_pascal_expanded k ks
      · constructor
        · intro ks
          exact multinomialFactorialQuotient_identity ks
        · constructor
          · intro n ks h
            exact multinomialFactorialDivisibility n ks h
          · intro ks
            exact multinomialIntegral_witness ks

end BEDC.Derived.MultinomialUp
