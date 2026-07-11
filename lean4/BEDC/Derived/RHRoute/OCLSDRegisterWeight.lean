import BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

/-
Canonical Fibonacci weight on the OCLSD PZG register (grounds the Fibonacci index).

Inspired by the innovation-geometry note "register norm² = log-time" (注记 7.6): the OCLSD
register `PZGRow` carries `(prime, Fibonacci-index)` atoms whose log-positions `F_k · log p`
were kept purely symbolic (OCLSDWeilGeometricAdapter).  This module supplies the arithmetic
that grounds that index: the per-prime Fibonacci weight of a register, and the fact that the
**Zeckendorf carry** `(p,k),(p,k+1) ↦ (p,k+2)` is an *isometry* of that weight
(`fib k + fib (k+1) = fib (k+2)`).  Hence the register's per-prime weight is the prime
valuation `v_p` read through its Zeckendorf digits, invariant under carry — the reason the
symbolic `Σ_{p,k} z_{p,k} F_k log p` collapses to `Σ_p v_p log p = log n = T` (the log-time,
命题 7.3 / cf. 定理 7.4 PZG completeness).

ζ-free, 0-axiom / propext-free (Nat recursion + `Nat.decEq`, no `Classical`).  Advances no
analytic gate: the `SpectralZeroIdentity` Hilbert–Pólya wall (OCLSDHamiltonian) is untouched.
-/

namespace BEDC.Derived.RHRoute.OCLSDRegisterWeight

open BEDC.Derived.RHRoute.OCLSDPhaseAlgebra

/-- Fibonacci numbers, `fib 0 = 0`, `fib 1 = 1`, `fib (k+2) = fib k + fib (k+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | Nat.succ (Nat.succ n) => fib n + fib (Nat.succ n)

/-- The defining Zeckendorf-carry recurrence, definitionally. -/
theorem fib_carry (k : Nat) : fib (Nat.succ (Nat.succ k)) = fib k + fib (Nat.succ k) :=
  rfl

/-- Per-prime Fibonacci weight of a register: sum of `fib (fibIndex)` over the atoms whose
prime equals `target`.  For a Zeckendorf register this is the valuation `v_target`. -/
def primeFibWeight (target : Nat) : PZGRow → Nat
  | PZGRow.nil => 0
  | PZGRow.cons q k rest =>
      (if q = target then fib k else 0) + primeFibWeight target rest

@[simp] theorem primeFibWeight_nil (target : Nat) :
    primeFibWeight target PZGRow.nil = 0 := rfl

theorem primeFibWeight_cons (target q k : Nat) (rest : PZGRow) :
    primeFibWeight target (PZGRow.cons q k rest)
      = (if q = target then fib k else 0) + primeFibWeight target rest := rfl

/-- **Zeckendorf carry is an isometry of the register weight** (注记 7.6): replacing the
adjacent atoms `(p,k),(p,k+1)` by `(p,k+2)` preserves every per-prime weight, because
`fib k + fib (k+1) = fib (k+2)`.  The register's per-prime Fibonacci content is therefore
carry-invariant — a well-defined valuation, not an artifact of the digit representation. -/
theorem primeFibWeight_carry (target p k : Nat) (rest : PZGRow) :
    primeFibWeight target
        (PZGRow.cons p k (PZGRow.cons p (Nat.succ k) rest))
      = primeFibWeight target (PZGRow.cons p (Nat.succ (Nat.succ k)) rest) := by
  rw [primeFibWeight_cons, primeFibWeight_cons, primeFibWeight_cons]
  by_cases h : p = target
  · rw [if_pos h, if_pos h, if_pos h, fib_carry, Nat.add_assoc]
  · rw [if_neg h, if_neg h, if_neg h, Nat.zero_add, Nat.zero_add]

/-- Propext-free `Nat` associativity (core `Nat.mul_assoc` depends on `propext`). -/
private theorem natMul_assoc (a b c : Nat) : a * b * c = a * (b * c) := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih => rw [Nat.mul_succ, Nat.mul_succ, ih, Nat.mul_add]

/-- Propext-free `Nat` power-add (core `Nat.pow_add` depends on `propext`). -/
private theorem natPow_add (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ n ih => rw [Nat.add_succ, Nat.pow_succ, ih, Nat.pow_succ, natMul_assoc]

/-- The integer a register encodes: `n(R) = ∏_{(p,k)∈R} p^{fib k}`.  Grouping the atoms by
prime gives `n = ∏_p p^{v_p}` with `v_p = primeFibWeight p` (定理 7.4 PZG completeness), so
the register norm² `Σ_{p,k} z_{p,k} F_k log p = log n(R) = T` is the log-time (命题 7.3):
`n` is the arithmetic carrier of the "register norm² = log-time" identity (注记 7.6). -/
def encodedNat : PZGRow → Nat
  | PZGRow.nil => 1
  | PZGRow.cons p k rest => p ^ (fib k) * encodedNat rest

@[simp] theorem encodedNat_nil : encodedNat PZGRow.nil = 1 := rfl

theorem encodedNat_cons (p k : Nat) (rest : PZGRow) :
    encodedNat (PZGRow.cons p k rest) = p ^ (fib k) * encodedNat rest := rfl

/-- **The Zeckendorf carry preserves the encoded integer** (hence preserves the log-time
`T = log n(R)`): `(p,k),(p,k+1) ↦ (p,k+2)` because `p^{fib k}·p^{fib (k+1)} = p^{fib (k+2)}`.
The register norm² `= log n(R)` is therefore carry-invariant — a well-defined `T`, not an
artifact of the digit representation. -/
theorem encodedNat_carry (p k : Nat) (rest : PZGRow) :
    encodedNat (PZGRow.cons p k (PZGRow.cons p (Nat.succ k) rest))
      = encodedNat (PZGRow.cons p (Nat.succ (Nat.succ k)) rest) := by
  rw [encodedNat_cons, encodedNat_cons, encodedNat_cons, fib_carry, natPow_add,
    natMul_assoc]

/-- **Register concatenation adds the per-prime weight**: `pzgAppend` is the ledger-append,
and the Fibonacci weight is additive under it (the accumulation half of the ledger monoid). -/
theorem primeFibWeight_append (target : Nat) (R1 R2 : PZGRow) :
    primeFibWeight target (pzgAppend R1 R2)
      = primeFibWeight target R1 + primeFibWeight target R2 := by
  induction R1 with
  | nil =>
      show primeFibWeight target R2 = 0 + primeFibWeight target R2
      rw [Nat.zero_add]
  | cons q k xs ih =>
      show primeFibWeight target (PZGRow.cons q k (pzgAppend xs R2))
        = primeFibWeight target (PZGRow.cons q k xs) + primeFibWeight target R2
      rw [primeFibWeight_cons, primeFibWeight_cons, ih, Nat.add_assoc]

/-- **Register concatenation multiplies the encoded integer**: `n(R1 ++ R2) = n(R1)·n(R2)`.
So `encodedNat` is a monoid homomorphism `(PZGRow, pzgAppend, nil) → (ℕ, ×, 1)` — the OCLSD
ledger's concatenation *is* integer multiplication (定理 7.4 completeness / 命题 7.3 additive
log-time `T = log n`, since `log` of this product is the sum of the parts). -/
theorem encodedNat_append (R1 R2 : PZGRow) :
    encodedNat (pzgAppend R1 R2) = encodedNat R1 * encodedNat R2 := by
  induction R1 with
  | nil =>
      show encodedNat R2 = encodedNat PZGRow.nil * encodedNat R2
      rw [encodedNat_nil, Nat.one_mul]
  | cons p k xs ih =>
      show encodedNat (PZGRow.cons p k (pzgAppend xs R2))
        = encodedNat (PZGRow.cons p k xs) * encodedNat R2
      rw [encodedNat_cons, encodedNat_cons, ih, natMul_assoc]

end BEDC.Derived.RHRoute.OCLSDRegisterWeight
