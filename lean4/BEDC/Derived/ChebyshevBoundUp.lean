import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.LucasTheoremBinomUp

namespace BEDC.Derived.ChebyshevBoundUp

open BEDC.Derived.BinomialIdentitiesUp
open BEDC.Derived.LucasTheoremBinomUp

/-!
Chebyshev 的 theta/psi 出口在本文件中用整数乘积与整除见证表达。
这避开实数对数，同时保留 BEDC 的 `NatPrimeUp` 素数接口。
-/

def natProduct : List Nat -> Nat
  | [] => 1
  | x :: xs => x * natProduct xs

def ThetaPrimeWindow (n primes : Nat) : List Nat -> Prop
  | ps =>
      ps.Nodup ∧
        (∀ p : Nat, p ∈ ps -> NatPrimeUp p ∧ p ≤ n) ∧
          (∀ p : Nat, NatPrimeUp p -> p ≤ n -> p ∈ ps) ∧
          primes = natProduct ps

def thetaPrimeProduct (primes : List Nat) : Nat :=
  natProduct primes

def thetaPrimeProductCarrier (n product : Nat) (primes : List Nat) : Prop :=
  ThetaPrimeWindow n product primes

def PsiPrimePowerWindow (n powers : Nat) : List (Nat × Nat) -> Prop
  | rows =>
      rows.Nodup ∧
        (∀ row : Nat × Nat, row ∈ rows ->
          NatPrimeUp row.1 ∧ 0 < row.2 ∧ row.1 ^ row.2 ≤ n) ∧
          (∀ row : Nat × Nat,
            NatPrimeUp row.1 -> 0 < row.2 -> row.1 ^ row.2 ≤ n -> row ∈ rows) ∧
            powers = natProduct (rows.map (fun row => row.1))

def psiPrimePowerProduct (powers : List (Nat × Nat)) : Nat :=
  natProduct (powers.map (fun row => row.1))

def psiPrimePowerProductCarrier
    (n product : Nat) (powers : List (Nat × Nat)) : Prop :=
  PsiPrimePowerWindow n product powers

def CentralBinomialDivisibility (n product : Nat) : Prop :=
  ∃ quotient : Nat, 0 < quotient ∧ C (n + n) n = product * quotient

private theorem two_pow_add_self_eq_four_pow (n : Nat) :
    2 ^ (n + n) = 4 ^ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        2 ^ (Nat.succ n + Nat.succ n) =
            2 ^ Nat.succ (Nat.succ (n + n)) := by
          rw [Nat.succ_add]
          rw [Nat.add_succ]
        _ = (2 ^ (n + n) * 2) * 2 := by
          rw [Nat.pow_succ]
          rw [Nat.pow_succ]
        _ = (4 ^ n * 2) * 2 := by
          rw [ih]
        _ = 4 ^ n * 4 := by
          rw [show (4 : Nat) = 2 + 2 by rfl]
          rw [Nat.mul_add]
          rw [Nat.mul_two]
        _ = 4 ^ Nat.succ n := by
          rw [Nat.pow_succ]

private theorem finiteFoldNatSum_last_term_le (f : Nat -> Nat) :
    ∀ k : Nat, f k ≤ finiteFoldNatSum f k
  | 0 => by
      change f 0 ≤ f 0
      exact Nat.le_refl (f 0)
  | Nat.succ k => by
      change f (Nat.succ k) ≤ finiteFoldNatSum f k + f (Nat.succ k)
      exact Nat.le_add_left (f (Nat.succ k)) (finiteFoldNatSum f k)

private theorem finiteFoldNatSum_extend_le (f : Nat -> Nat) :
    ∀ k extra : Nat, finiteFoldNatSum f k ≤ finiteFoldNatSum f (k + extra)
  | k, 0 => by
      rw [Nat.add_zero]
      exact Nat.le_refl (finiteFoldNatSum f k)
  | k, Nat.succ extra => by
      have ih := finiteFoldNatSum_extend_le f k extra
      have step : finiteFoldNatSum f (k + extra) ≤
          finiteFoldNatSum f (Nat.succ (k + extra)) := by
        change finiteFoldNatSum f (k + extra) ≤
          finiteFoldNatSum f (k + extra) + f (Nat.succ (k + extra))
        exact Nat.le_add_right
          (finiteFoldNatSum f (k + extra)) (f (Nat.succ (k + extra)))
      rw [Nat.add_succ]
      exact Nat.le_trans ih step

private theorem nat_le_mul_of_positive_right (a q : Nat) :
    0 < q -> a ≤ a * q := by
  cases q with
  | zero =>
      intro positive
      cases positive
  | succ q =>
      intro _positive
      rw [Nat.mul_succ]
      exact Nat.le_add_left a (a * q)

theorem centralBinomial_le_rowSum (n : Nat) :
    C (n + n) n ≤ rowSum (n + n) := by
  unfold rowSum rowPrefixSum
  exact Nat.le_trans
    (finiteFoldNatSum_last_term_le (fun k => C (n + n) k) n)
    (finiteFoldNatSum_extend_le (fun k => C (n + n) k) n n)

theorem centralBinomial_le_four_pow (n : Nat) :
    C (n + n) n ≤ 4 ^ n := by
  calc
    C (n + n) n ≤ rowSum (n + n) := centralBinomial_le_rowSum n
    _ = 2 ^ (n + n) := binomial_row_sum (n + n)
    _ = 4 ^ n := two_pow_add_self_eq_four_pow n

theorem thetaPrimeProduct_bound_from_central_divisibility
    {n product : Nat} {primes : List Nat}
    (_carrier : thetaPrimeProductCarrier n product primes)
    (centralWitness : CentralBinomialDivisibility n product) :
    product ≤ 4 ^ n := by
  cases centralWitness with
  | intro quotient quotientData =>
      have productLeCentral : product ≤ C (n + n) n := by
        rw [quotientData.right]
        exact nat_le_mul_of_positive_right product quotient quotientData.left
      exact Nat.le_trans productLeCentral (centralBinomial_le_four_pow n)

theorem thetaPrimeProduct_bound
    (n : Nat) (primes : List Nat)
    (window : ThetaPrimeWindow n (thetaPrimeProduct primes) primes)
    (centralWitness : CentralBinomialDivisibility n (thetaPrimeProduct primes)) :
    thetaPrimeProduct primes ≤ 4 ^ n := by
  exact thetaPrimeProduct_bound_from_central_divisibility
    (n := n) (primes := primes) window centralWitness

theorem thetaPrimeProduct_carrier_self
    {n : Nat} {primes : List Nat} :
    ThetaPrimeWindow n (thetaPrimeProduct primes) primes ->
      thetaPrimeProductCarrier n (thetaPrimeProduct primes) primes := by
  intro window
  exact window

theorem psiPrimePowerProduct_carrier_self
    {n : Nat} {powers : List (Nat × Nat)} :
    PsiPrimePowerWindow n (psiPrimePowerProduct powers) powers ->
      psiPrimePowerProductCarrier n (psiPrimePowerProduct powers) powers := by
  intro window
  exact window

theorem ChebyshevBoundUp_constructive_export :
    (∀ n : Nat, C (n + n) n ≤ 4 ^ n) ∧
      (∀ n : Nat, ∀ primes : List Nat,
        ThetaPrimeWindow n (thetaPrimeProduct primes) primes ->
          thetaPrimeProductCarrier n (thetaPrimeProduct primes) primes) ∧
      (∀ n : Nat, ∀ powers : List (Nat × Nat),
        PsiPrimePowerWindow n (psiPrimePowerProduct powers) powers ->
          psiPrimePowerProductCarrier n (psiPrimePowerProduct powers) powers) ∧
      (∀ n : Nat, ∀ primes : List Nat,
        ThetaPrimeWindow n (thetaPrimeProduct primes) primes ->
          CentralBinomialDivisibility n (thetaPrimeProduct primes) ->
            thetaPrimeProduct primes ≤ 4 ^ n) := by
  constructor
  · intro n
    exact centralBinomial_le_four_pow n
  · constructor
    · intro n primes window
      exact thetaPrimeProduct_carrier_self window
    · constructor
      · intro n powers window
        exact psiPrimePowerProduct_carrier_self window
      · intro n primes window centralWitness
        exact thetaPrimeProduct_bound n primes window centralWitness

end BEDC.Derived.ChebyshevBoundUp
