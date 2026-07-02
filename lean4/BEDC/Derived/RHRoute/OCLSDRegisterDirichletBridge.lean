import BEDC.Derived.RHRoute.OCLSDRegisterWeight
import BEDC.Derived.RHRoute.FiniteEulerDirichlet
import BEDC.Derived.FibonacciUp
import BEDC.Derived.ZeckendorfUp

/-
S3 Layer 1 — OCLSD register → finite Euler–Dirichlet bridge (pointwise Nat kernel).

After S1 (Weyl gate) disproved "OCLSD spectrum = zeta zeros" for the BC-locked log-n generator,
S3 supplies the correct Bost–Connes side: the OCLSD prime–Fibonacci register maps *canonically*
onto Loning's encoded-Dirichlet interface, so the existing finite Euler–Dirichlet theorem
(`FiniteEulerDirichlet.finiteEuler_eq_encodedDirichlet`) can be consumed by OCLSD WITHOUT
changing the register semantics.

This module is only the pointwise Nat bridge `encodedNat R = encNat (pzgToExponents R)` under the
index map `(p,k) ↦ (p, fib k)`.  It does NOT reprove Euler = Dirichlet — that theorem, the
encoded-Dirichlet term machinery and the unique-factorization core all belong to Loning's
`FiniteEulerDirichlet` / `PrimeUp` lanes and are consumed here, not re-derived.  0-axiom /
propext-free.
-/

namespace BEDC.Derived.RHRoute.OCLSDRegisterDirichletBridge

open BEDC.Derived.RHRoute.OCLSDRegisterWeight
open BEDC.Derived.RHRoute.OCLSDPhaseAlgebra
open BEDC.Derived.RHRoute.FiniteEulerDirichlet
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp (natToUnary natToUnary_length)
open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)

/-- Propext-free `a*b*c = a*(b*c)` (core `Nat.mul_assoc` depends on propext). -/
private theorem natMul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, ih]

/-- Propext-free `0 * a = 0`. -/
private theorem natZero_mul (a : Nat) : 0 * a = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => rw [Nat.mul_succ, ih]

/-- Propext-free `a*b = b*a` (core `Nat.mul_comm` depends on propext). -/
private theorem natMul_comm (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => rw [Nat.mul_zero, natZero_mul]
  | succ b ih => rw [Nat.mul_succ, Nat.succ_mul, ih]

/-- `primeFlatProductNat` (∏ of `bwordLength`) is multiplicative over list append. -/
private theorem primeFlatProductNat_append :
    ∀ (xs ys : List BHist),
      primeFlatProductNat (xs ++ ys)
        = primeFlatProductNat xs * primeFlatProductNat ys
  | [], ys => (Nat.one_mul (primeFlatProductNat ys)).symm
  | x :: xs, ys => by
      show bwordLength x * primeFlatProductNat (xs ++ ys)
        = bwordLength x * primeFlatProductNat xs * primeFlatProductNat ys
      rw [primeFlatProductNat_append xs ys, natMul_assoc]

/-- `primeFlatProductNat (replicate e q) = (bwordLength q) ^ e`. -/
private theorem primeFlatProductNat_replicate (q : BHist) :
    ∀ e : Nat, primeFlatProductNat (List.replicate e q) = (bwordLength q) ^ e
  | 0 => rfl
  | Nat.succ e => by
      show bwordLength q * primeFlatProductNat (List.replicate e q)
        = (bwordLength q) ^ (Nat.succ e)
      rw [primeFlatProductNat_replicate q e, Nat.pow_succ, natMul_comm]

/-- `encNat [] = 1`. -/
theorem encNat_nil : encNat ([] : List (Nat × Nat)) = 1 := rfl

/-- **Consing one prime-exponent atom multiplies in `p^e`.** -/
theorem encNat_cons (p e : Nat) (xs : List (Nat × Nat)) :
    encNat ((p, e) :: xs) = p ^ e * encNat xs := by
  show primeFlatProductNat (List.replicate e (natToUnary p) ++ exponentSpine xs)
    = p ^ e * primeFlatProductNat (exponentSpine xs)
  rw [primeFlatProductNat_append, primeFlatProductNat_replicate, natToUnary_length]

/-- Register → Loning exponent vector under `(p,k) ↦ (p, fib k)`. -/
def pzgToExponents : PZGRow → List (Nat × Nat)
  | PZGRow.nil => []
  | PZGRow.cons p k rest => (p, fib k) :: pzgToExponents rest

/-- **S3 Layer-1 load-bearing bridge**: the OCLSD register's encoded integer is exactly Loning's
`encNat` of the Fibonacci-mapped exponent vector.  Pure `Nat`, no prime uniqueness needed — this
is the adapter kernel that lets OCLSD consume the finite Euler–Dirichlet machinery. -/
theorem encodedNat_eq_encNat_fibmap :
    ∀ R : PZGRow, encodedNat R = encNat (pzgToExponents R)
  | PZGRow.nil => rfl
  | PZGRow.cons p k rest => by
      show p ^ (fib k) * encodedNat rest
        = encNat ((p, fib k) :: pzgToExponents rest)
      rw [encNat_cons, encodedNat_eq_encNat_fibmap rest]

/-! ## Layer 2 — canonical Zeckendorf register realizes `p^e` (uses Loning's `zeckendorf_sum_restore`). -/

/-- The OCLSD register's Fibonacci equals the shared `FibonacciUp.fib` (same standard Fibonacci;
only the addition order in the recurrence differs). -/
private theorem fib_eq_pair : ∀ n : Nat,
    fib n = BEDC.Derived.FibonacciUp.fib n
      ∧ fib (n + 1) = BEDC.Derived.FibonacciUp.fib (n + 1)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
      obtain ⟨h0, h1⟩ := fib_eq_pair n
      refine ⟨h1, ?_⟩
      show fib n + fib (n + 1)
        = BEDC.Derived.FibonacciUp.fib (n + 1) + BEDC.Derived.FibonacciUp.fib n
      rw [h0, h1, Nat.add_comm]

theorem fib_eq (n : Nat) : fib n = BEDC.Derived.FibonacciUp.fib n := (fib_eq_pair n).1

/-- Propext-free `a^(m+n) = a^m * a^n`. -/
private theorem natPow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, natMul_assoc]

/-- Register built from a prime's Zeckendorf index list: `index ↦ (p, index+2)`. -/
def pzgFromIndices (p : Nat) : List Nat → PZGRow
  | [] => PZGRow.nil
  | index :: rest => PZGRow.cons p (index + 2) (pzgFromIndices p rest)

/-- Sum of `fib (index+2)` over a Zeckendorf index list. -/
def sumMyFib : List Nat → Nat
  | [] => 0
  | index :: rest => fib (index + 2) + sumMyFib rest

theorem sumMyFib_eq_zeckendorfValue (indices : List Nat) :
    sumMyFib indices = BEDC.Derived.ZeckendorfUp.zeckendorfValue indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      show fib (index + 2) + sumMyFib rest
        = BEDC.Derived.ZeckendorfUp.fibonacciTerm index
          + BEDC.Derived.ZeckendorfUp.zeckendorfValue rest
      unfold BEDC.Derived.ZeckendorfUp.fibonacciTerm
      rw [ih, fib_eq (index + 2)]

theorem encodedNat_pzgFromIndices (p : Nat) (indices : List Nat) :
    encodedNat (pzgFromIndices p indices) = p ^ (sumMyFib indices) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      show p ^ (fib (index + 2)) * encodedNat (pzgFromIndices p rest)
        = p ^ (fib (index + 2) + sumMyFib rest)
      rw [ih, natPow_add]

/-- Canonical Zeckendorf register realizing exponent `e` on prime `p` (NOT a raw multiset). -/
def pzgOfExponent (p e : Nat) : PZGRow :=
  pzgFromIndices p (BEDC.Derived.ZeckendorfUp.zeckendorf e)

/-- **S3 Layer-2 core**: the canonical Zeckendorf register on prime `p` encodes exactly `p^e`,
because `Σ fib(index+2) = e` (Loning's `zeckendorf_sum_restore`, consumed not re-derived).  This
is the genuine Zeckendorf increment: OCLSD's Fibonacci register realizes an arbitrary prime power
canonically. -/
theorem encodedNat_pzgOfExponent (p e : Nat) :
    encodedNat (pzgOfExponent p e) = p ^ e := by
  show encodedNat (pzgFromIndices p (BEDC.Derived.ZeckendorfUp.zeckendorf e)) = p ^ e
  rw [encodedNat_pzgFromIndices, sumMyFib_eq_zeckendorfValue,
    BEDC.Derived.ZeckendorfUp.zeckendorf_sum_restore]

/-- Multi-prime canonical register from an exponent vector `[(p,e),…]`. -/
def pzgOfExponentVector : List (Nat × Nat) → PZGRow
  | [] => PZGRow.nil
  | (p, e) :: rest => pzgAppend (pzgOfExponent p e) (pzgOfExponentVector rest)

/-- **S3 Layer-2 (multi-prime)**: the canonical Zeckendorf register of an exponent vector encodes
exactly Loning's `encNat` of it.  Combines the per-prime Zeckendorf realization
(`encodedNat_pzgOfExponent`) with the register-concatenation homomorphism (`encodedNat_append`, O3)
and `encNat_cons`.  This is the register side of the finite Euler–Dirichlet correspondence, ready
to feed Loning's `finiteEuler_eq_encodedDirichlet` at the window level. -/
theorem encodedNat_pzgOfExponentVector (xs : List (Nat × Nat)) :
    encodedNat (pzgOfExponentVector xs) = encNat xs := by
  induction xs with
  | nil => rfl
  | cons pe rest ih =>
      obtain ⟨p, e⟩ := pe
      show encodedNat (pzgAppend (pzgOfExponent p e) (pzgOfExponentVector rest))
        = encNat ((p, e) :: rest)
      rw [encodedNat_append, encodedNat_pzgOfExponent, ih, encNat_cons]

end BEDC.Derived.RHRoute.OCLSDRegisterDirichletBridge
