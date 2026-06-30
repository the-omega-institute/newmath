import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.PochhammerUp
import BEDC.Derived.RationalUp.Core
import BEDC.Derived.VandermondeChuUp

namespace BEDC.Derived.Hypergeometric2F1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev RatNum : Type :=
  BEDC.Derived.RationalUp.RatNum

abbrev Z : Type :=
  BEDC.Derived.PochhammerUp.Z

abbrev Zeq : Z -> Z -> Prop :=
  BEDC.Derived.PochhammerUp.Zeq

def integerRing : BEDC.Algebra.Rel.RelCommRing Z Zeq :=
  BEDC.Derived.PochhammerUp.integerRing

def ratOfNat (n : Nat) : RatNum :=
  BEDC.Derived.RationalUp.intToRat
    (BEDC.Derived.RationalUp.intOfNat (natToUnary n) (natToUnary_unary n))

def ascPochhammerNat (a : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ k => ascPochhammerNat a k * (a + k)

theorem ascPochhammerNat_succ (a k : Nat) :
    ascPochhammerNat a (Nat.succ k) = ascPochhammerNat a k * (a + k) := by
  rfl

theorem ascPochhammerNat_zero (a : Nat) :
    ascPochhammerNat a 0 = 1 := by
  rfl

theorem ascPochhammerNat_one (a : Nat) :
    ascPochhammerNat a 1 = a := by
  change 1 * (a + 0) = a
  rw [Nat.add_zero]
  exact Nat.one_mul a

theorem ascPochhammerNat_two (a : Nat) :
    ascPochhammerNat a 2 = a * (a + 1) := by
  rw [ascPochhammerNat_succ]
  rw [ascPochhammerNat_one]

theorem ascPochhammerInt_succ (x : Z) (k : Nat) :
    Zeq (BEDC.Derived.PochhammerUp.ascPochhammerInt x (Nat.succ k))
      (integerRing.mul (BEDC.Derived.PochhammerUp.ascPochhammerInt x k)
        (integerRing.add x (BEDC.Derived.PochhammerUp.intOfNatStd k))) := by
  exact BEDC.Derived.PochhammerUp.ascPochhammerInt_succ x k

theorem ascPochhammerInt_small_values (x : Z) :
    Zeq (BEDC.Derived.PochhammerUp.ascPochhammerInt x 0) integerRing.one ∧
      Zeq (BEDC.Derived.PochhammerUp.ascPochhammerInt x 1) x := by
  exact
    ⟨BEDC.Derived.PochhammerUp.ascPochhammerInt_zero x,
      BEDC.Derived.PochhammerUp.ascPochhammerInt_one x⟩

def natPow (z : Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ k => natPow z k * z

theorem natPow_zero (z : Nat) :
    natPow z 0 = 1 := by
  rfl

theorem natPow_succ (z k : Nat) :
    natPow z (Nat.succ k) = natPow z k * z := by
  rfl

structure TwoFOneNatTerm where
  index : Nat
  numeratorLeft : Nat
  numeratorRight : Nat
  denominatorPochhammer : Nat
  factorial : Nat
  zPower : Nat
  deriving DecidableEq, Repr

structure TwoFOneFiniteTruncation where
  a : RatNum
  b : RatNum
  c : RatNum
  z : RatNum
  cutoff : Nat
  terms : List TwoFOneNatTerm

def twoFOneNatTerm (a b c z k : Nat) : TwoFOneNatTerm :=
  { index := k
    numeratorLeft := ascPochhammerNat a k
    numeratorRight := ascPochhammerNat b k
    denominatorPochhammer := ascPochhammerNat c k
    factorial := BEDC.Derived.PochhammerUp.natFactorialCount k
    zPower := natPow z k }

def twoFOneNatTermsFrom (a b c z : Nat) : Nat -> Nat -> List TwoFOneNatTerm
  | 0, _k => []
  | Nat.succ fuel, k =>
      twoFOneNatTerm a b c z k ::
        twoFOneNatTermsFrom a b c z fuel (Nat.succ k)

def twoFOneFiniteTruncationOfNat
    (a b c z cutoff : Nat) : TwoFOneFiniteTruncation :=
  { a := ratOfNat a
    b := ratOfNat b
    c := ratOfNat c
    z := ratOfNat z
    cutoff := cutoff
    terms := twoFOneNatTermsFrom a b c z (Nat.succ cutoff) 0 }

theorem twoFOneNatTermsFrom_zero (a b c z k : Nat) :
    twoFOneNatTermsFrom a b c z 0 k = [] := by
  rfl

theorem twoFOneNatTermsFrom_succ (a b c z fuel k : Nat) :
    twoFOneNatTermsFrom a b c z (Nat.succ fuel) k =
      twoFOneNatTerm a b c z k ::
        twoFOneNatTermsFrom a b c z fuel (Nat.succ k) := by
  rfl

theorem twoFOneFiniteTruncation_terms_zero (a b c z : Nat) :
    (twoFOneFiniteTruncationOfNat a b c z 0).terms =
      [twoFOneNatTerm a b c z 0] := by
  rfl

theorem twoFOneNatTerm_zero (a b c z : Nat) :
    twoFOneNatTerm a b c z 0 =
      { index := 0
        numeratorLeft := 1
        numeratorRight := 1
        denominatorPochhammer := 1
        factorial := 1
        zPower := 1 } := by
  unfold twoFOneNatTerm ascPochhammerNat natPow
  rw [BEDC.Derived.PochhammerUp.natFactorialCount_zero]

theorem twoFOneNatTerm_succ_pochhammer (a b c z k : Nat) :
    (twoFOneNatTerm a b c z (Nat.succ k)).numeratorLeft =
        (twoFOneNatTerm a b c z k).numeratorLeft * (a + k) ∧
      (twoFOneNatTerm a b c z (Nat.succ k)).numeratorRight =
        (twoFOneNatTerm a b c z k).numeratorRight * (b + k) ∧
      (twoFOneNatTerm a b c z (Nat.succ k)).denominatorPochhammer =
        (twoFOneNatTerm a b c z k).denominatorPochhammer * (c + k) := by
  exact ⟨rfl, rfl, rfl⟩

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def chuVandermondeFiniteSum (m n p : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.vandermondeSum m n p

theorem chuVandermondeFiniteSum_unfold_zero (m n : Nat) :
    chuVandermondeFiniteSum m n 0 = C m 0 * C n 0 := by
  rfl

theorem chuVandermondeFiniteSum_unfold_succ (m n p : Nat) :
    chuVandermondeFiniteSum m n (Nat.succ p) =
      C m 0 * C n (Nat.succ p) +
        BEDC.Derived.BinomialIdentitiesUp.vandermondeDiagonalSum m n 1 p := by
  rfl

theorem chu_vandermonde_finite (m n p : Nat) :
    chuVandermondeFiniteSum m n p = C (m + n) p := by
  exact BEDC.Derived.VandermondeChuUp.chu_vandermonde m n p

def chuVandermondeAntiDiagonalSumFrom
    (m n total offset : Nat) : Nat -> Nat
  | 0 => C m offset * C n (total - offset)
  | Nat.succ fuel =>
      C m offset * C n (total - offset) +
        chuVandermondeAntiDiagonalSumFrom m n total (Nat.succ offset) fuel

def chuVandermondeAntiDiagonalSum (m n p : Nat) : Nat :=
  chuVandermondeAntiDiagonalSumFrom m n p 0 p

private theorem add_sub_left_clean (offset fuel : Nat) :
    offset + fuel - offset = fuel := by
  induction offset with
  | zero =>
      rw [Nat.zero_add]
      exact Nat.sub_zero fuel
  | succ offset ih =>
      rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]
      exact ih

private theorem add_succ_eq_succ_add (offset fuel : Nat) :
    offset + Nat.succ fuel = Nat.succ offset + fuel := by
  rw [Nat.add_succ]
  rw [Nat.succ_add]

private theorem chuVandermondeAntiDiagonalSumFrom_matches_diagonal
    (m n offset : Nat) :
    ∀ fuel : Nat,
      chuVandermondeAntiDiagonalSumFrom m n (offset + fuel) offset fuel =
        BEDC.Derived.BinomialIdentitiesUp.vandermondeDiagonalSum
          m n offset fuel
  | 0 => by
      change C m offset * C n (offset - offset) =
        C m offset * C n 0
      rw [Nat.sub_self]
  | Nat.succ fuel => by
      change C m offset * C n (offset + Nat.succ fuel - offset) +
          chuVandermondeAntiDiagonalSumFrom
            m n (offset + Nat.succ fuel) (Nat.succ offset) fuel =
        C m offset * C n (Nat.succ fuel) +
          BEDC.Derived.BinomialIdentitiesUp.vandermondeDiagonalSum
            m n (Nat.succ offset) fuel
      rw [add_sub_left_clean offset (Nat.succ fuel)]
      rw [add_succ_eq_succ_add offset fuel]
      rw [chuVandermondeAntiDiagonalSumFrom_matches_diagonal
        m n (Nat.succ offset) fuel]

theorem chuVandermondeAntiDiagonalSum_unfold_zero (m n : Nat) :
    chuVandermondeAntiDiagonalSum m n 0 = C m 0 * C n 0 := by
  rfl

theorem chuVandermondeAntiDiagonalSum_unfold_succ (m n p : Nat) :
    chuVandermondeAntiDiagonalSum m n (Nat.succ p) =
      C m 0 * C n (Nat.succ p) +
        chuVandermondeAntiDiagonalSumFrom m n (Nat.succ p) 1 p := by
  rfl

theorem chu_vandermonde_antidiagonal (m n p : Nat) :
    chuVandermondeAntiDiagonalSum m n p = C (m + n) p := by
  unfold chuVandermondeAntiDiagonalSum
  have diagonal :=
    chuVandermondeAntiDiagonalSumFrom_matches_diagonal m n 0 p
  rw [Nat.zero_add] at diagonal
  rw [diagonal]
  exact chu_vandermonde_finite m n p

theorem Hypergeometric2F1Up_constructive_export :
    (∀ a k : Nat,
      ascPochhammerNat a (Nat.succ k) = ascPochhammerNat a k * (a + k)) ∧
      (∀ a : Nat, ascPochhammerNat a 0 = 1) ∧
      (∀ a : Nat, ascPochhammerNat a 1 = a) ∧
      (∀ m n p : Nat, chuVandermondeAntiDiagonalSum m n p = C (m + n) p) ∧
      (∀ a b c z : Nat,
        (twoFOneFiniteTruncationOfNat a b c z 0).terms =
          [twoFOneNatTerm a b c z 0]) := by
  constructor
  · intro a k
    exact ascPochhammerNat_succ a k
  · constructor
    · intro a
      exact ascPochhammerNat_zero a
    · constructor
      · intro a
        exact ascPochhammerNat_one a
      · constructor
        · intro m n p
          exact chu_vandermonde_antidiagonal m n p
        · intro a b c z
          exact twoFOneFiniteTruncation_terms_zero a b c z

end BEDC.Derived.Hypergeometric2F1Up
