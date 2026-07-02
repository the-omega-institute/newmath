import BEDC.Derived.RHRoute.OCLSDRegisterWeight
import BEDC.Derived.RHRoute.FiniteEulerDirichlet

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

end BEDC.Derived.RHRoute.OCLSDRegisterDirichletBridge
